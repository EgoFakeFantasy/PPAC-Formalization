/- Pinned ProductNames.actionHom: (permuteOrderIso pi).withTopCongr.
Top is the internal empty set and coe p is the internal singleton {p}.
Identity/composition and the source product order are transported exactly. -/
import PPAC.Migration.ForcingWithTopCarrier

namespace PPAC.Migration.ForcingWithTopAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingWithTopCarrier
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Lifted (r z t : M.Carrier .set) : Prop := (Empty z ∧ Empty t) ∨
  ∃ p q, Single z p ∧ Single t q ∧ PureKuratowski.PairMember M p q r

def lifted {m : Nat} (r z t : Fin m) : Formula m :=
  ((empty z).conj (empty t)).disj (.ex (.ex
    ((single z.castSucc.castSucc (Fin.last m).castSucc).conj
      ((single t.castSucc.castSucc (Fin.last (m+1))).conj
        (Source.SetLanguage.edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))))

theorem lifted_semantics {m : Nat} (env : Fin m → M.Carrier .set) (r z t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (lifted r z t) ↔
      Lifted (env r) (env z) (env t) := by
  simp only [lifted, Lifted, Formula.Realize, empty_semantics (M := M), single_semantics (M := M),
    KuratowskiZF.source_edge, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def Graph (W r a : M.Carrier .set) : Prop :=
  ∀ z t, PureKuratowski.PairMember M z t a ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z W ∧ Lifted r z t

def graph {m : Nat} (W r a : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc W.castSucc.castSucc).conj
      (lifted r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem graph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (W r a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (graph W r a) ↔
      Graph (env W) (env r) (env a) := by
  simp only [graph, Graph, Source.Formula.iff, Formula.Realize, lifted_semantics (M := M),
    KuratowskiZF.source_edge, Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z t => ⟨(h z t).1, (h z t).2⟩, fun h z t => ⟨(h z t).mp, (h z t).mpr⟩⟩

theorem lifted_coe {r z t p q : M.Carrier .set} (hz : Single z p) (ht : Single t q) :
    Lifted r z t ↔ PureKuratowski.PairMember M p q r := by
  constructor
  · rintro (⟨he, _⟩ | ⟨p', q', hz', ht', hpq⟩)
    · exact False.elim (single_nonempty hz he)
    · have hp := single_injective hz hz'
      have hq := single_injective ht ht'
      exact hp.symm ▸ hq.symm ▸ hpq
  · intro hpq
    exact Or.inr ⟨p, q, hz, ht, hpq⟩

theorem lifted_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {P r z t s : M.Carrier .set} (hr : Endomap P r) (ht : Lifted r z t) (hs : Lifted r z s) : t = s := by
  rcases ht with ⟨hz, ht⟩ | ⟨p, q, hz, ht, hpq⟩
  · rcases hs with ⟨_, hs⟩ | ⟨p, q, hz', _, _⟩
    · exact empty_unique hM ht hs
    · exact False.elim (single_nonempty hz' hz)
  · rcases hs with ⟨hz', _⟩ | ⟨p', q', hz', hs, hpq'⟩
    · exact False.elim (single_nonempty hz hz')
    · have hp := single_injective hz hz'
      have hq := function_unique hr.1 hpq (hp.symm ▸ hpq')
      exact single_unique hM ht (hq.symm ▸ hs)

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF)
    {P W r : M.Carrier .set} (hW : Carrier P W) (hr : Permutation P r) :
    ∃ a, Permutation W a ∧ Graph W r a := by
  let params := Source.SetLanguage.args1 r
  let query := lifted (0 : Fin 1).castSucc.castSucc (Fin.last 1).castSucc (Fin.last 2)
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 1 :=
    { bound := fun j => params j.rev, free := fun _ => W }
  have hRel : ∀ z t, (ProjectSyntax.binary query).denote env z t ↔ Lifted r z t := by
    intro z t
    rw [ForcingMapConditions.binary_semantics hM query params W z t]
    simp only [ForcingMapConditions.MapRel, query, lifted_semantics (M := M), params,
      Fin.lastCases_last, Fin.lastCases_castSucc]
    rfl
  obtain ⟨a, ha, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := W) (target := W)
    (fun z hz => by
      rcases (hW z).mp hz with hz | ⟨p, hp, hz⟩
      · exact ⟨z, (hRel z z).mpr (Or.inl ⟨hz, hz⟩)⟩
      · obtain ⟨q, hpq, _⟩ := hr.1.1.2 p hp
        obtain ⟨t, ht⟩ := exists_single hM q
        exact ⟨t, (hRel z t).mpr (Or.inr ⟨p, q, hz, ht, hpq⟩)⟩)
    (fun z _ t s ht hs => lifted_unique hM hr.1 ((hRel z t).mp ht) ((hRel z s).mp hs))
    (fun z t _ ht => by
      rcases (hRel z t).mp ht with ⟨_, ht⟩ | ⟨p, q, _, ht, hpq⟩
      · exact (hW t).mpr (Or.inl ht)
      · exact (hW t).mpr (Or.inr ⟨q, hr.1.2 p q hpq, ht⟩))
  have hg : Graph W r a := fun z t => (he z t).trans (and_congr Iff.rfl (hRel z t))
  refine ⟨a, ⟨(native_endomap hM W a).mpr ha, ?_, ?_⟩, hg⟩
  · intro z t s hzs hts
    rcases ((hg z s).mp hzs).2 with ⟨hz, hs⟩ | ⟨p, q, hz, hs, hpq⟩
    · rcases ((hg t s).mp hts).2 with ⟨ht, _⟩ | ⟨p, q, _, hs', _⟩
      · exact empty_unique hM hz ht
      · exact False.elim (single_nonempty hs' hs)
    · rcases ((hg t s).mp hts).2 with ⟨_, hs'⟩ | ⟨p', q', ht, hs', hpq'⟩
      · exact False.elim (single_nonempty hs hs')
      · have hq := single_injective hs hs'
        have hp := hr.2.1 p p' q hpq (hq.symm ▸ hpq')
        exact single_unique hM hz (hp.symm ▸ ht)
  · intro t ht
    rcases (hW t).mp ht with het | ⟨q, hq, htq⟩
    · exact ⟨t, ht, (hg t t).mpr ⟨ht, Or.inl ⟨het, het⟩⟩⟩
    · obtain ⟨p, hp, hpq⟩ := hr.2.2 q hq
      obtain ⟨z, hz⟩ := exists_single hM p
      have hzW := (hW z).mpr (Or.inr ⟨p, hp, hz⟩)
      exact ⟨z, hzW, (hg z t).mpr ⟨hzW, Or.inr ⟨p, q, hz, htq, hpq⟩⟩⟩

theorem top_fixed {P W r a e : M.Carrier .set} (hW : Carrier P W)
    (hg : Graph W r a) (he : Empty e) : PureKuratowski.PairMember M e e a :=
  (hg e e).mpr ⟨(hW e).mpr (Or.inl he), Or.inl ⟨he, he⟩⟩

theorem graph_coe {P W r a z t p q : M.Carrier .set} (hW : Carrier P W)
    (hg : Graph W r a) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (hz : Single z p) (ht : Single t q) :
    PureKuratowski.PairMember M z t a ↔ PureKuratowski.PairMember M p q r := by
  rw [hg z t, lifted_coe hz ht]
  exact ⟨fun h => h.2, fun h => ⟨(hW z).mpr (Or.inr ⟨p, hp, hz⟩), h⟩⟩

theorem graph_identity (hM : FirstOrder.Theory.Models M nativeZF)
    {P W r a : M.Carrier .set} (ha : Endomap W a) (hr : IdentityGraph P r)
    (hg : Graph W r a) : IdentityGraph W a := by
  have hfix : ∀ z t, PureKuratowski.PairMember M z t a → z = t := by
    intro z t hzt
    rcases ((hg z t).mp hzt).2 with ⟨hz, ht⟩ | ⟨p, q, hz, ht, hpq⟩
    · exact empty_unique hM hz ht
    · exact single_unique hM hz (((hr p q).mp hpq).2.symm ▸ ht)
  intro z t
  constructor
  · intro hzt
    exact ⟨function_input ha.1 hzt, hfix z t hzt⟩
  · rintro ⟨hz, rfl⟩
    obtain ⟨t, hzt, _⟩ := ha.1.2 z hz
    exact (hfix z t hzt).symm ▸ hzt

theorem lifted_composition {P r s u z w t : M.Carrier .set}
    (hs : Endomap P s) (hc : CompositionGraph P r s u)
    (hsz : Lifted s z w) (hrw : Lifted r w t) : Lifted u z t := by
  rcases hsz with ⟨hz, hw⟩ | ⟨p, q, hz, hw, hpq⟩
  · rcases hrw with ⟨_, ht⟩ | ⟨p, q, hw', _, _⟩
    · exact Or.inl ⟨hz, ht⟩
    · exact False.elim (single_nonempty hw' hw)
  · rcases hrw with ⟨hw', _⟩ | ⟨q', v, hw', ht, hqv⟩
    · exact False.elim (single_nonempty hw hw')
    · have hq := single_injective hw hw'
      exact Or.inr ⟨p, v, hz, ht,
        (hc p v).mpr ⟨function_input hs.1 hpq, q, hpq, hq.symm ▸ hqv⟩⟩

theorem lifted_factor (hM : FirstOrder.Theory.Models M nativeZF)
    {P r s u z t : M.Carrier .set} (hc : CompositionGraph P r s u) (hu : Lifted u z t) :
    ∃ w, Lifted s z w ∧ Lifted r w t := by
  rcases hu with ⟨hz, ht⟩ | ⟨p, q, hz, ht, hpq⟩
  · exact ⟨z, Or.inl ⟨hz, hz⟩, Or.inl ⟨hz, ht⟩⟩
  · obtain ⟨_, v, hpv, hvq⟩ := (hc p q).mp hpq
    obtain ⟨w, hw⟩ := exists_single hM v
    exact ⟨w, Or.inr ⟨p, v, hz, hw, hpv⟩, Or.inr ⟨v, q, hw, ht, hvq⟩⟩

theorem graph_multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {P W r s u a b c : M.Carrier .set} (hs : Endomap P s) (hb : Endomap W b)
    (hc : CompositionGraph P r s u) (hga : Graph W r a) (hgb : Graph W s b) (hgc : Graph W u c) :
    CompositionGraph W a b c := by
  intro z t
  constructor
  · intro hzt
    obtain ⟨hz, hu⟩ := (hgc z t).mp hzt
    obtain ⟨w, hsw, hrw⟩ := lifted_factor hM hc hu
    have hzw := (hgb z w).mpr ⟨hz, hsw⟩
    exact ⟨hz, w, hzw, (hga w t).mpr ⟨hb.2 z w hzw, hrw⟩⟩
  · rintro ⟨hz, w, hzw, hwt⟩
    exact (hgc z t).mpr ⟨hz, lifted_composition hs hc ((hgb z w).mp hzw).2 ((hga w t).mp hwt).2⟩

/-- Literal WithTop relation: every element is below top; coe order is the source product order. -/
def Le (D mul z t : M.Carrier .set) : Prop := Empty t ∨
  ∃ p q, Single z p ∧ Single t q ∧ ForcingProductAction.Le D mul p q

def le {m : Nat} (D mul z t : Fin m) : Formula m :=
  (empty t).disj (.ex (.ex ((single z.castSucc.castSucc (Fin.last m).castSucc).conj
    ((single t.castSucc.castSucc (Fin.last (m+1))).conj
      (ForcingProductAction.le D.castSucc.castSucc mul.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1)))))))

theorem le_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul z t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (le D mul z t) ↔
      Le (env D) (env mul) (env z) (env t) := by
  simp only [le, Le, Formula.Realize, empty_semantics (M := M), single_semantics (M := M),
    ForcingProductAction.le_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem le_coe {D mul z t p q : M.Carrier .set} (hz : Single z p) (ht : Single t q) :
    Le D mul z t ↔ ForcingProductAction.Le D mul p q := by
  constructor
  · rintro (he | ⟨p', q', hz', ht', hpq⟩)
    · exact False.elim (single_nonempty ht he)
    · have hp := single_injective hz hz'
      have hq := single_injective ht ht'
      exact hp.symm ▸ hq.symm ▸ hpq
  · intro hpq
    exact Or.inr ⟨p, q, hz, ht, hpq⟩

theorem not_top_le_coe {D mul z t q : M.Carrier .set} (hz : Empty z) (ht : Single t q) : ¬ Le D mul z t := by
  rintro (he | ⟨p, q, hz', _, _⟩)
  · exact single_nonempty ht he
  · exact single_nonempty hz' hz

def OrderPreserving (D mul a : M.Carrier .set) : Prop :=
  ∀ z t Z T, PureKuratowski.PairMember M z Z a → PureKuratowski.PairMember M t T a →
    (Le D mul z t ↔ Le D mul Z T)

def orderPreserving {m : Nat} (D mul a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let z := (Fin.last m).castSucc.castSucc.castSucc
  let t := (Fin.last (m+1)).castSucc.castSucc
  let Z := (Fin.last (m+2)).castSucc
  let T := Fin.last (m+3)
  .all (.all (.all (.all ((Source.SetLanguage.edge (up a) z Z).imp
    ((Source.SetLanguage.edge (up a) t T).imp ((le (up D) (up mul) z t).iff (le (up D) (up mul) Z T)))))))

theorem orderPreserving_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (orderPreserving D mul a) ↔
      OrderPreserving (env D) (env mul) (env a) := by
  simp only [orderPreserving, OrderPreserving, Source.Formula.iff, Formula.Realize,
    KuratowskiZF.source_edge, le_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z t Z T hz ht => ⟨(h z t Z T hz ht).1, (h z t Z T hz ht).2⟩,
    fun h z t Z T hz ht => ⟨(h z t Z T hz ht).mp, (h z t Z T hz ht).mpr⟩⟩

theorem graph_order {D mul W r a : M.Carrier .set}
    (hr : ForcingProductAction.OrderPreserving D mul r) (hg : Graph W r a) : OrderPreserving D mul a := by
  intro z t Z T hz ht
  rcases ((hg z Z).mp hz).2 with ⟨hz, hZ⟩ | ⟨p, P, hz, hZ, hpP⟩
  · rcases ((hg t T).mp ht).2 with ⟨ht, hT⟩ | ⟨q, Q, ht, hT, _⟩
    · exact ⟨fun _ => Or.inl hT, fun _ => Or.inl ht⟩
    · exact ⟨fun h => False.elim (not_top_le_coe hz ht h), fun h => False.elim (not_top_le_coe hZ hT h)⟩
  · rcases ((hg t T).mp ht).2 with ⟨ht, hT⟩ | ⟨q, Q, ht, hT, hqQ⟩
    · exact ⟨fun _ => Or.inl hT, fun _ => Or.inl ht⟩
    · rw [le_coe hz ht, le_coe hZ hT]
      exact hr p q P Q hpP hqQ

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF) (D mul P : M.Carrier .set)
    {r : M.Carrier .set} (hr : Permutation P r) (ho : ForcingProductAction.OrderPreserving D mul r) :
    ∃ W e a, Carrier P W ∧ Empty e ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem e W ∧
      Permutation W a ∧ Graph W r a ∧ PureKuratowski.PairMember M e e a ∧ OrderPreserving D mul a := by
  obtain ⟨W, hW⟩ := exists_carrier hM P
  obtain ⟨e, he⟩ := exists_empty hM
  obtain ⟨a, ha, hg⟩ := exists_action hM hW hr
  exact ⟨W, e, a, hW, he, (hW e).mpr (Or.inl he), ha, hg, top_fixed hW hg he, graph_order ho hg⟩

def identitySentence : Source.Sentence :=
  ((endomap (1 : Fin 4) 3).imp ((identityGraph (0 : Fin 4) 2).imp ((graph (1 : Fin 4) 2 3).imp ((identityGraph (1 : Fin 4) 3))))).close

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2
  apply (identityGraph_semantics (M := M) env 1 3).mpr
  exact graph_identity hM
    ((endomap_semantics (M := M) env 1 3).mp h0)
    ((identityGraph_semantics (M := M) env 0 2).mp h1)
    ((graph_semantics (M := M) env 1 2 3).mp h2)

theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)

def multiplicationSentence : Source.Sentence :=
  ((endomap (0 : Fin 8) 3).imp ((endomap (1 : Fin 8) 6).imp ((compositionGraph (0 : Fin 8) 2 3 4).imp ((graph (1 : Fin 8) 2 5).imp ((graph (1 : Fin 8) 3 6).imp ((graph (1 : Fin 8) 4 7).imp ((compositionGraph (1 : Fin 8) 5 6 7)))))))).close

theorem multiplication_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence multiplicationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2 h3 h4 h5
  apply (compositionGraph_semantics (M := M) env 1 5 6 7).mpr
  exact graph_multiplication hM
    ((endomap_semantics (M := M) env 0 3).mp h0)
    ((endomap_semantics (M := M) env 1 6).mp h1)
    ((compositionGraph_semantics (M := M) env 0 2 3 4).mp h2)
    ((graph_semantics (M := M) env 1 2 5).mp h3)
    ((graph_semantics (M := M) env 1 3 6).mp h4)
    ((graph_semantics (M := M) env 1 4 7).mp h5)

theorem multiplication_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence multiplicationSentence) :=
  ModelTransfer.derives (fun _ hM => multiplication_models hM)

def constructionSentence : Source.Sentence :=
  ((permutation (2 : Fin 4) 3).imp ((ForcingProductAction.orderPreserving 0 1 3).imp
    (.ex (.ex (.ex ((carrier (2 : Fin 4).castSucc.castSucc.castSucc (Fin.last 4).castSucc.castSucc).conj
      ((empty (Fin.last 5).castSucc).conj
        ((Formula.mem (Fin.last 5).castSucc (Fin.last 4).castSucc.castSucc).conj
          ((permutation (Fin.last 4).castSucc.castSucc (Fin.last 6)).conj
            ((graph (Fin.last 4).castSucc.castSucc (3 : Fin 4).castSucc.castSucc.castSucc (Fin.last 6)).conj
              ((Source.SetLanguage.edge (Fin.last 6) (Fin.last 5).castSucc (Fin.last 5).castSucc).conj
                (orderPreserving (0 : Fin 4).castSucc.castSucc.castSucc (1 : Fin 4).castSucc.castSucc.castSucc (Fin.last 6))))))))))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr ho
  obtain ⟨W, e, a, hW, he, heW, ha, hg, hfix, hoa⟩ := exists_system hM (env 0) (env 1) (env 2)
    ((permutation_semantics (M := M) env 2 3).mp hr)
    ((ForcingProductAction.orderPreserving_semantics (M := M) env 0 1 3).mp ho)
  let v : Fin 7 → M.Carrier .set := Fin.lastCases a (Fin.lastCases e (Fin.lastCases W env))
  refine ⟨W, e, a, ?_, ?_, heW, ?_, ?_, ?_, ?_⟩
  · apply (carrier_semantics (M := M) v (2 : Fin 4).castSucc.castSucc.castSucc (Fin.last 4).castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hW
  · apply (empty_semantics (M := M) v (Fin.last 5).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using he
  · apply (permutation_semantics (M := M) v (Fin.last 4).castSucc.castSucc (Fin.last 6)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ha
  · apply (graph_semantics (M := M) v (Fin.last 4).castSucc.castSucc (3 : Fin 4).castSucc.castSucc.castSucc (Fin.last 6)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hg
  · apply (KuratowskiZF.source_edge (M := M) v (Fin.last 6) (Fin.last 5).castSucc (Fin.last 5).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hfix
  · apply (orderPreserving_semantics (M := M) v (0 : Fin 4).castSucc.castSucc.castSucc
      (1 : Fin 4).castSucc.castSucc.castSucc (Fin.last 6)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hoa

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingWithTopAction
