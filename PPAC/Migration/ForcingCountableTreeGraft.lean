/- Source AssignedGraphs.CountableHull.exists_closed:322: the full omega-ary
node constructor. Adapt donor Borel.Graft/GraftTree/GraftWellFounded to the
source two-component (nodes, Option-A labels) code; no host well-foundedness. -/
import PPAC.Migration.ForcingCountableTreeCodes

namespace PPAC.Migration.ForcingCountableTreeGraft
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ExistingTreeAddresses ForcingCountableTreeCodes
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sub (H i T F : M.Domain) : Prop := ∃ c, M.PairMember I i c H ∧ I.Codes c T F

def sub {n} (H i T F : Term n) : Formula 1 n := .existsE (.conj
  (Formula.orderedPairMem 𝒞 i.weaken .newest H.weaken) (𝒞.code .newest T.weaken F.weaken))
derive_free_closed sub

theorem sub_semantics {n} (ρ : Env M n) (H i T F : Term n) :
    Formula.satisfies ρ (sub (𝒞 := 𝒞) H i T F) ↔ Sub I (H.eval ρ) (i.eval ρ) (T.eval ρ) (F.eval ρ) := by
  simp only [sub, Sub, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

theorem sub_valid {w S A z R C H i T F : M.Domain} (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (h : Sub I H i T F) :
    M.mem i w ∧ Tree I w S A z R T F := by
  obtain ⟨c, hi, hc⟩ := h
  obtain ⟨T', F', hc', ht⟩ := (hC c).mp (hH.output_mem_of_pairMember hi)
  obtain ⟨rfl, rfl⟩ := I.injective hc hc'
  exact ⟨hH.input_mem_of_pairMember hi, ht⟩

theorem sub_unique {H i T F U G : M.Domain} (hH : M.IsSetFunction I H)
    (h : Sub I H i T F) (k : Sub I H i U G) : T = U ∧ F = G := by
  obtain ⟨c, hi, hc⟩ := h
  obtain ⟨d, hj, hd⟩ := k
  exact I.injective hc (hH.2 i d c hj hi ▸ hd)

def Shift (z H t s F : M.Domain) : Prop := ∃ i T, Sub I H i T F ∧ M.mem s T ∧ Cons_d I z i s t

def shift {n} (z H t s F : Term n) : Formula 1 n := .existsE (.existsE (.conj
  (sub (𝒞 := 𝒞) H.weaken.weaken (.bound 1) .newest F.weaken.weaken)
  (.conj (.mem s.weaken.weaken .newest)
    (cons_m (𝒞 := 𝒞) z.weaken.weaken (.bound 1) s.weaken.weaken t.weaken.weaken))))
derive_free_closed shift

theorem shift_semantics {n} (hE : Extensional M) (ρ : Env M n) (z H t s F : Term n) :
    Formula.satisfies ρ (shift (𝒞 := 𝒞) z H t s F) ↔
      Shift I (z.eval ρ) (H.eval ρ) (t.eval ρ) (s.eval ρ) (F.eval ρ) := by
  simp only [shift, Shift, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sub_semantics I, Formula.satisfies_mem_iff, cons_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem shift_type (hZF : M.Models ZF) {w S A z R C H t s F : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (h : Shift I z H t s F) : M.mem t S ∧ t ≠ z := by
  obtain ⟨i, T, hc, hs, ht⟩ := h
  obtain ⟨hi, hT⟩ := sub_valid I hC hH hc
  obtain ⟨n, hn, hsf⟩ := (hS s).mp (hT.1 s hs)
  obtain ⟨k, hk, _, htf⟩ := cons_type_l I hZF hw hz hi hn hsf ht
  exact ⟨(hS t).mpr ⟨k, hk, htf⟩, cons_ne_empty_l I hz ht⟩

theorem shift_unique (hZF : M.Models ZF) {w S A z R C H t s F r G : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (h : Shift I z H t s F) (k : Shift I z H t r G) :
    s = r ∧ F = G := by
  obtain ⟨i, T, hc, hs, ht⟩ := h
  obtain ⟨j, U, hd, hr, hu⟩ := k
  have hT := (sub_valid I hC hH hc).2
  have hU := (sub_valid I hC hH hd).2
  obtain ⟨n, hn, hsf⟩ := (hS s).mp (hT.1 s hs)
  obtain ⟨m, hm, hrf⟩ := (hS r).mp (hU.1 r hr)
  obtain ⟨e, es⟩ := cons_injective_l I hZF hw hz hn hm hsf hrf ht hu
  subst j
  exact ⟨es, (sub_unique I hH.1 hc hd).2⟩

/-- Literal new root and disjoint indexed copies of every child tree. -/
def Graft (z H a T F : M.Domain) : Prop :=
  (∀ t, M.mem t T ↔ t = z ∨ ∃ s G, Shift I z H t s G) ∧ M.IsSetRelation I F ∧
  ∀ t x, M.PairMember I t x F ↔ (t = z ∧ x = a) ∨
    ∃ s G, Shift I z H t s G ∧ M.PairMember I s x G

def graft {n} (z H a T F : Term n) : Formula 1 n := .conj
  (.forallE (.iff (.mem .newest T.weaken) (.disj (Formula.extensionalEq .newest z.weaken)
    (.existsE (.existsE (shift (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))
  (.conj (Formula.isRelation 𝒞 F) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) z.weaken.weaken)
      (Formula.extensionalEq .newest a.weaken.weaken)) (.existsE (.existsE (.conj
        (shift (𝒞 := 𝒞) z.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
        (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 2) .newest)))))))))
derive_free_closed graft

theorem graft_semantics {n} (hE : Extensional M) (ρ : Env M n) (z H a T F : Term n) :
    Formula.satisfies ρ (graft (𝒞 := 𝒞) z H a T F) ↔
      Graft I (z.eval ρ) (H.eval ρ) (a.eval ρ) (T.eval ρ) (F.eval ρ) := by
  simp only [graft, Graft, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff,
    shift_semantics I hE, Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]
  rfl

theorem graft_exists (hZF : M.Models ZF) {w S A z R C H a : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (ha : M.mem a A) : ∃ T F, Graft I z H a T F := by
  have hzS : M.mem z S := (hS z).mpr ⟨z, hzw, ds_empty_fun_l I hz⟩
  let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push H).push a
  let φ : UnarySchema 3 := {body := (.disj (Formula.extensionalEq .newest (.bound 3))
    (.existsE (.existsE (shift (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 2) (.bound 1) .newest))))}
  have hφ t : φ.denote ρ t ↔ t = z ∨ ∃ s G, Shift I z H t s G := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff, shift_semantics I hZF.1]
    rfl
  obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ S
  have hn t : M.mem t T ↔ t = z ∨ ∃ s G, Shift I z H t s G := by
    refine (hT t).trans ⟨fun h => (hφ t).mp h.2, fun h => ⟨?_, (hφ t).mpr h⟩⟩
    exact h.elim (fun e => e.symm ▸ hzS) (fun ⟨_, _, h⟩ => (shift_type I hZF hw hS hz hC hH h).1)
  obtain ⟨SA, hSA⟩ := ZF.exists_cartesianProduct hZF I S A
  let ψ : UnarySchema 3 := {body := .existsE (.existsE (.conj (𝒞.code (.bound 2) (.bound 1) .newest)
    (.disj (.conj (Formula.extensionalEq (.bound 1) (.bound 5)) (Formula.extensionalEq .newest (.bound 3)))
      (.existsE (.existsE (.conj (shift (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 3) (.bound 1) .newest)
        (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 2) .newest)))))))}
  have hψ p : ψ.denote ρ p ↔ ∃ t x, I.Codes p t x ∧
      ((t = z ∧ x = a) ∨ ∃ s G, Shift I z H t s G ∧ M.PairMember I s x G) := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      shift_semantics I hZF.1, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF ψ ρ SA
  refine ⟨T, F, hn, (fun p hp => ?_), fun t x => ?_⟩
  · obtain ⟨t, _, x, _, hc⟩ := (hSA p).mp ((hF p).mp hp).1
    exact ⟨t, x, hc⟩
  · constructor
    · rintro ⟨p, hc, hp⟩
      obtain ⟨t', x', hc', h⟩ := (hψ p).mp ((hF p).mp hp).2
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      exact h
    · intro h
      have bounds : M.mem t S ∧ M.mem x A := by
        rcases h with ⟨rfl, rfl⟩ | ⟨s, G, hs, hx⟩
        · exact ⟨hzS, ha⟩
        · have ht := (shift_type I hZF hw hS hz hC hH hs).1
          obtain ⟨i, U, hc, _, _⟩ := hs
          exact ⟨ht, ((sub_valid I hC hH hc).2.2.2.2.2.2.1 s x hx).2⟩
      obtain ⟨p, hp⟩ := I.total t x
      exact ⟨p, hp, (hF p).mpr ⟨(hSA p).mpr ⟨t, bounds.1, x, bounds.2, hp⟩,
        (hψ p).mpr ⟨t, x, hp, h⟩⟩⟩


theorem graft_nodes (hZF : M.Models ZF) {w S A z R C H a T F : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F) :
    M.MemberSubset T S ∧ M.mem z T ∧
      ∀ t, M.mem t T → ∀ u, M.mem u S → M.MemberSubset u t → M.mem u T := by
  have hzS := (hS z).mpr ⟨z, hzw, ds_empty_fun_l I hz⟩
  refine ⟨fun t ht => ?_, (hG.1 z).mpr (Or.inl rfl), ?_⟩
  · exact ((hG.1 t).mp ht).elim (fun e => e.symm ▸ hzS)
      (fun ⟨_, _, h⟩ => (shift_type I hZF hw hS hz hC hH h).1)
  · intro t ht u hu hut
    apply (hG.1 u).mpr
    rcases (hG.1 t).mp ht with e | ⟨s, G, i, U, hc, hs, ht⟩
    · exact Or.inl (hZF.1.eq_of_same_members u z (fun p =>
        iff_of_false (fun hp => hz p (e ▸ hut p hp)) (hz p)))
    · rcases cons_cases_l I hZF hw hS hz hu with e | ⟨j, r, _, hr, hu⟩
      · exact Or.inl e
      · obtain ⟨n, hn, hrf⟩ := (hS r).mp hr
        obtain ⟨e, hrs⟩ := (cons_subset_l I hZF hw hz hn hrf hu ht).mp hut
        subst j
        have hU := (sub_valid I hC hH hc).2
        exact Or.inr ⟨r, G, i, U, hc, hU.2.2.1 s hs r hr hrs, hu⟩

theorem graft_labels (hZF : M.Models ZF) {w S A z R C H a T F t s G : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F)
    (h : Shift I z H t s G) (x : M.Domain) : M.PairMember I t x F ↔ M.PairMember I s x G := by
  refine (hG.2.2 t x).trans ⟨?_, fun hx => Or.inr ⟨s, G, h, hx⟩⟩
  rintro (⟨e, _⟩ | ⟨r, V, k, hx⟩)
  · exact ((shift_type I hZF hw hS hz hC hH h).2 e).elim
  · obtain ⟨rfl, rfl⟩ := shift_unique I hZF hw hS hz hC hH h k
    exact hx

theorem graft_root (hZF : M.Models ZF) {w S A z R C H a T F : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F) (x : M.Domain) :
    M.PairMember I z x F ↔ x = a := by
  refine (hG.2.2 z x).trans ⟨?_, fun e => Or.inl ⟨rfl, e⟩⟩
  rintro (⟨_, e⟩ | ⟨_, _, h, _⟩)
  · exact e
  · exact ((shift_type I hZF hw hS hz hC hH h).2 rfl).elim

/-- Inside a shifted subtree, every child comes from the SAME original child tree. -/
theorem graft_child (hZF : M.Models ZF) {w S A z R C H a T F i U G s t v : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hR : Edges I w S R) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F)
    (hc : Sub I H i U G) (hs : M.mem s U) (ht : Cons_d I z i s t)
    (hv : M.mem v T) (he : M.PairMember I v t R) :
    ∃ r, M.mem r U ∧ Cons_d I z i r v ∧ M.PairMember I r s R := by
  obtain ⟨hi, hU⟩ := sub_valid I hC hH hc
  obtain ⟨n, hn, hsf⟩ := (hS s).mp (hU.1 s hs)
  have htv := ((hR.2 v t).mp he).2.2
  rcases (hG.1 v).mp hv with e | ⟨r, G', j, U', hc', hr, hv⟩
  · exact (tree_step_not_empty_l I hz (e ▸ htv)).elim
  · obtain ⟨hj, hU'⟩ := sub_valid I hC hH hc'
    obtain ⟨m, hm, hrf⟩ := (hS r).mp (hU'.1 r hr)
    obtain ⟨e, hsr⟩ := (cons_step_l I hZF hw hz hi hj hn hm hsf hrf ht hv).mp htv
    subst j
    obtain ⟨rfl, rfl⟩ := sub_unique I hH.1 hc hc'
    exact ⟨r, hr, hv, (hR.2 r s).mpr ⟨hU'.1 s hs, hU'.1 r hr, hsr⟩⟩

/-- Donor subset-minimum proof, adapted to full labelled tree codes. -/
theorem graft_wellFounded (hZF : M.Models ZF) {w S A z R C H a T F : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hR : Edges I w S R) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F) :
    ForcingCountableTreeEvaluation.WellFounded I T R := by
  classical
  intro Y hY hn
  by_cases h : ∃ t, M.mem t Y ∧ t ≠ z
  · obtain ⟨t, htY, htz⟩ := h
    obtain ⟨s, G, i, U, hc, hs, ht⟩ := ((hG.1 t).mp (hY t htY)).resolve_left htz
    let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push i).push Y
    let φ : UnarySchema 3 := {body := (Formula.existsMem (.bound 1)
      (cons_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest))}
    obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ U
    have hD r : M.mem r D ↔ M.mem r U ∧ ∃ v, M.mem v Y ∧ Cons_d I z i r v := by
      simp only [φ, Formula.satisfies_existsMem_iff, cons_sat_l I hZF.1] at hD'
      exact hD' r
    have hU := (sub_valid I hC hH hc).2
    obtain ⟨r, hr, hmin⟩ := hU.2.2.2.1 D (fun r hr => ((hD r).mp hr).1)
      ⟨s, (hD s).mpr ⟨hs, t, htY, ht⟩⟩
    obtain ⟨hrU, v, hvY, hv⟩ := (hD r).mp hr
    refine ⟨v, hvY, fun b hb he => ?_⟩
    obtain ⟨q, hq, hqb, hqr⟩ := graft_child I hZF hw hS hz hR hC hH hG hc hrU hv (hY b hb) he
    exact hmin q ((hD q).mpr ⟨hq, b, hb, hqb⟩) hqr
  · obtain ⟨t, ht⟩ := hn
    refine ⟨t, ht, fun b hb he => ?_⟩
    have eb : b = z := Classical.byContradiction (fun e => h ⟨b, hb, e⟩)
    exact tree_step_not_empty_l I hz (eb ▸ ((hR.2 b t).mp he).2.2)

/-- Every shifted labelled node has exactly ALL its old natural children;
the new root has one subtree for every internal natural index. -/
theorem graft_full (hZF : M.Models ZF) {w S A z R C H a T F : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F) :
    ∀ t, M.mem t T → ∀ v, M.mem v S → Step_d I w t v →
      (M.mem v T ↔ ∃ x, M.PairMember I t x F) := by
  intro t ht v hv htv
  rcases (hG.1 t).mp ht with e | hsG
  · subst t
    have hvT : M.mem v T := by
      rcases cons_cases_l I hZF hw hS hz hv with e | ⟨i, r, hi, hr, hrv⟩
      · exact (tree_step_not_empty_l I hz (e ▸ htv)).elim
      · have er := (cons_root_l I hZF hw hS hz hzw hi hr hrv).mp htv
        subst r
        obtain ⟨c, hc, hic⟩ := hH.2.2 i hi
        obtain ⟨U, G, hcode, hU⟩ := (hC c).mp hc
        exact (hG.1 v).mpr (Or.inr ⟨z, G, i, U, ⟨c, hic, hcode⟩, hU.2.1, hrv⟩)
    exact ⟨fun _ => ⟨a, (graft_root I hZF hw hS hz hC hH hG a).mpr rfl⟩, fun _ => hvT⟩
  · obtain ⟨s, G, hsG⟩ := hsG
    have lab := graft_labels I hZF hw hS hz hC hH hG hsG
    obtain ⟨i, U, hc, hs, hst⟩ := hsG
    obtain ⟨hi, hU⟩ := sub_valid I hC hH hc
    obtain ⟨n, hn, hsf⟩ := (hS s).mp (hU.1 s hs)
    constructor
    · intro hvT
      have htS := (shift_type I hZF hw hS hz hC hH ⟨i, U, hc, hs, hst⟩).1
      obtain ⟨r, hr, _, hrs⟩ := graft_child I hZF hw hS hz hR hC hH hG hc hs hst hvT
        ((hR.2 v t).mpr ⟨htS, hv, htv⟩)
      obtain ⟨x, hx⟩ := (hU.2.2.2.2.2.2 s hs r (hU.1 r hr) ((hR.2 r s).mp hrs).2.2).mp hr
      exact ⟨x, (lab x).mpr hx⟩
    · rintro ⟨x, hx⟩
      have hsx := (lab x).mp hx
      rcases cons_cases_l I hZF hw hS hz hv with e | ⟨j, r, hj, hr, hrv⟩
      · exact (tree_step_not_empty_l I hz (e ▸ htv)).elim
      · obtain ⟨m, hm, hrf⟩ := (hS r).mp hr
        obtain ⟨e, hsr⟩ := (cons_step_l I hZF hw hz hi hj hn hm hsf hrf hst hrv).mp htv
        subst j
        have hrU := (hU.2.2.2.2.2.2 s hs r hr hsr).mpr ⟨x, hsx⟩
        exact (hG.1 v).mpr (Or.inr ⟨r, G, i, U, hc, hrU, hrv⟩)

theorem graft_tree (hZF : M.Models ZF) {w S A z R C H a T F : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C)
    (ha : M.mem a A) (hG : Graft I z H a T F) : Tree I w S A z R T F := by
  have nodes := graft_nodes I hZF hw hS hz hzw hC hH hG
  have hfun : M.IsSetFunction I F := by
    refine ⟨hG.2.1, fun t x y hx hy => ?_⟩
    rcases (hG.2.2 t x).mp hx with ⟨rfl, rfl⟩ | ⟨s, G, hsG, hxG⟩
    · exact ((graft_root I hZF hw hS hz hC hH hG y).mp hy).symm
    · have hyG := (graft_labels I hZF hw hS hz hC hH hG hsG y).mp hy
      obtain ⟨i, U, hc, _, _⟩ := hsG
      exact (sub_valid I hC hH hc).2.2.2.2.2.1.2 s x y hxG hyG
  refine ⟨nodes.1, nodes.2.1, nodes.2.2, graft_wellFounded I hZF hw hS hz hR hC hH hG,
    hfun, ?_, graft_full I hZF hw hS hz hzw hR hC hH hG⟩
  intro t x hx
  rcases (hG.2.2 t x).mp hx with ⟨rfl, rfl⟩ | ⟨s, G, hsG, hxG⟩
  · exact ⟨nodes.2.1, ha⟩
  · refine ⟨(hG.1 t).mpr (Or.inr ⟨s, G, hsG⟩), ?_⟩
    obtain ⟨i, U, hc, _, _⟩ := hsG
    exact ((sub_valid I hC hH hc).2.2.2.2.2.2.1 s x hxG).2

theorem closed (hZF : M.Models ZF) {w S A z R C H a : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C) (ha : M.mem a A) :
    ∃ T F c, Graft I z H a T F ∧ I.Codes c T F ∧ M.mem c C := by
  obtain ⟨T, F, hG⟩ := graft_exists I hZF hw hS hz hzw hC hH ha
  obtain ⟨c, hc⟩ := I.total T F
  exact ⟨T, F, c, hG, hc, (hC c).mpr ⟨T, F, hc, graft_tree I hZF hw hS hz hzw hR hC hH ha hG⟩⟩


def closure {n} (z H a C : Term n) : Formula 1 n := .existsE (.existsE (.existsE (.conj
  (graft (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken a.weaken.weaken.weaken (.bound 2) (.bound 1))
  (.conj (𝒞.code .newest (.bound 2) (.bound 1)) (.mem .newest C.weaken.weaken.weaken)))))
derive_free_closed closure

theorem closure_semantics {n} (hE : Extensional M) (ρ : Env M n) (z H a C : Term n) :
    Formula.satisfies ρ (closure (𝒞 := 𝒞) z H a C) ↔ ∃ T F c,
      Graft I (z.eval ρ) (H.eval ρ) (a.eval ρ) T F ∧ I.Codes c T F ∧ M.mem c (C.eval ρ) := by
  simp only [closure, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    graft_semantics I hE, I.satisfies_code_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

/-- Every internal omega-family of valid source trees has its labelled node in C. -/
def closureSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 8 (.imp (Formula.isOmega (.bound 0))
    (.imp (ExistingFiniteSequenceBounds.fseq_space_m (𝒞 := 𝒞) (.bound 0) (.bound 0) (.bound 1))
    (.imp (.forallE (.neg (.mem .newest (.bound 4))))
    (.imp (.mem (.bound 3) (.bound 0))
    (.imp (edges (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 4))
    (.imp (carrier (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5))
    (.imp (Formula.isFunctionFromTo 𝒞 (.bound 6) (.bound 0) (.bound 5))
    (.imp (.mem (.bound 7) (.bound 2))
    (closure (𝒞 := 𝒞) (.bound 3) (.bound 6) (.bound 7) (.bound 5))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
theorem closure_models (hZF : M.Models ZF) : M.SatisfiesSentence (closureSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
    ExistingFiniteSequenceBounds.fseq_space_sat_l I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    edges_semantics I hZF.1, carrier_semantics I hZF.1, Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    closure_semantics I hZF.1]
  exact fun hw hS hz hzw hR hC hH ha => closed I hZF hw hS hz hzw hR hC hH ha

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

theorem closure_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (closureSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro M hM
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mpr
    (closure_models (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingCountableTreeGraft
