/- Pinned ProductForcing.permute and permuteOrderIso: simultaneous exact
transport of the Cohen and diagram coordinates. Component carriers/actions
are supplied by their already constructed internal graphs. -/
import PPAC.Migration.ForcingCohenActionLaws
import PPAC.Migration.ForcingDiagramOrder

namespace PPAC.Migration.ForcingProductAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingCohenCoordinates (Cartesian cartesian cartesian_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Tensor (a b z t : M.Carrier .set) : Prop :=
  ∃ x y u v, PureKuratowski.Code M z x y ∧ PureKuratowski.PairMember M x u a ∧
    PureKuratowski.PairMember M y v b ∧ PureKuratowski.Code M t u v

def tensor {m : Nat} (a b z t : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let x := (Fin.last m).castSucc.castSucc.castSucc
  let y := (Fin.last (m+1)).castSucc.castSucc
  let u := (Fin.last (m+2)).castSucc
  let v := Fin.last (m+3)
  .ex (.ex (.ex (.ex ((PairSyntax.ordered (up z) x y).conj
    ((Source.SetLanguage.edge (up a) x u).conj
      ((Source.SetLanguage.edge (up b) y v).conj (PairSyntax.ordered (up t) u v)))))))

theorem tensor_semantics {m : Nat} (env : Fin m → M.Carrier .set) (a b z t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (tensor a b z t) ↔
      Tensor (env a) (env b) (env z) (env t) := by
  simp only [tensor, Tensor, Formula.Realize, KuratowskiZF.source_code, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def Graph (P a b r : M.Carrier .set) : Prop :=
  ∀ z t, PureKuratowski.PairMember M z t r ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z P ∧ Tensor a b z t

def graph {m : Nat} (P a b r : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc P.castSucc.castSucc).conj
      (tensor a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem graph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (P a b r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (graph P a b r) ↔
      Graph (env P) (env a) (env b) (env r) := by
  simp only [graph, Graph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    tensor_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z t => ⟨(h z t).1, (h z t).2⟩, fun h z t => ⟨(h z t).mp, (h z t).mpr⟩⟩

theorem tensor_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {X Y a b z t s : M.Carrier .set} (ha : Endomap X a) (hb : Endomap Y b)
    (ht : Tensor a b z t) (hs : Tensor a b z s) : t = s := by
  obtain ⟨x, y, u, v, hz, hxu, hyv, ht⟩ := ht
  obtain ⟨x', y', u', v', hz', hxu', hyv', hs⟩ := hs
  obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hz hz'
  have hu := function_unique ha.1 hxu hxu'
  have hv := function_unique hb.1 hyv hyv'
  exact KuratowskiZF.code_unique hM ht (hu ▸ hv ▸ hs)

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF)
    {X Y P a b : M.Carrier .set} (hP : Cartesian X Y P)
    (ha : Permutation X a) (hb : Permutation Y b) : ∃ r, Permutation P r ∧ Graph P a b r := by
  let params := Source.SetLanguage.args2 a b
  let query := tensor (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc
    (Fin.last 2).castSucc (Fin.last 3)
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := fun j => params j.rev, free := fun _ => P }
  have hRel : ∀ z t, (ProjectSyntax.binary query).denote env z t ↔ Tensor a b z t := by
    intro z t
    rw [ForcingMapConditions.binary_semantics hM query params P z t]
    simp only [ForcingMapConditions.MapRel, query, tensor_semantics (M := M), params,
      Fin.lastCases_last, Fin.lastCases_castSucc]
    rfl
  obtain ⟨r, hr, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := P) (target := P)
    (fun z hz => by
      obtain ⟨x, hx, y, hy, hz⟩ := (hP z).mp hz
      obtain ⟨u, hxu, _⟩ := ha.1.1.2 x hx
      obtain ⟨v, hyv, _⟩ := hb.1.1.2 y hy
      obtain ⟨t, ht⟩ := KuratowskiZF.exists_code hM u v
      exact ⟨t, (hRel z t).mpr ⟨x, y, u, v, hz, hxu, hyv, ht⟩⟩)
    (fun z _ t s ht hs => tensor_unique hM ha.1 hb.1 ((hRel z t).mp ht) ((hRel z s).mp hs))
    (fun z t _ ht => by
      obtain ⟨x, y, u, v, _, hxu, hyv, ht⟩ := (hRel z t).mp ht
      exact (hP t).mpr ⟨u, ha.1.2 x u hxu, v, hb.1.2 y v hyv, ht⟩)
  have hg : Graph P a b r := fun z t => (he z t).trans (and_congr Iff.rfl (hRel z t))
  refine ⟨r, ⟨(native_endomap hM P r).mpr hr, ?_, ?_⟩, hg⟩
  · intro z t s hzs hts
    obtain ⟨_, x, y, u, v, hz, hxu, hyv, hs⟩ := (hg z s).mp hzs
    obtain ⟨_, x', y', u', v', ht, hxu', hyv', hs'⟩ := (hg t s).mp hts
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hs hs'
    have hx := ha.2.1 x x' u hxu hxu'
    have hy := hb.2.1 y y' v hyv hyv'
    exact KuratowskiZF.code_unique hM hz (hx ▸ hy ▸ ht)
  · intro t ht
    obtain ⟨u, hu, v, hv, ht⟩ := (hP t).mp ht
    obtain ⟨x, hx, hxu⟩ := ha.2.2 u hu
    obtain ⟨y, hy, hyv⟩ := hb.2.2 v hv
    obtain ⟨z, hz⟩ := KuratowskiZF.exists_code hM x y
    have hzP := (hP z).mpr ⟨x, hx, y, hy, hz⟩
    exact ⟨z, hzP, (hg z t).mpr ⟨hzP, x, y, u, v, hz, hxu, hyv, ht⟩⟩

theorem graph_identity (hM : FirstOrder.Theory.Models M nativeZF)
    {X Y P a b r : M.Carrier .set} (hr : Endomap P r)
    (ha : IdentityGraph X a) (hb : IdentityGraph Y b) (hg : Graph P a b r) : IdentityGraph P r := by
  have hfix : ∀ z t, PureKuratowski.PairMember M z t r → z = t := by
    intro z t hzt
    obtain ⟨_, x, y, u, v, hz, hxu, hyv, ht⟩ := (hg z t).mp hzt
    have hx := ((ha x u).mp hxu).2
    have hy := ((hb y v).mp hyv).2
    exact KuratowskiZF.code_unique hM hz (hx ▸ hy ▸ ht)
  intro z t
  constructor
  · intro hzt
    exact ⟨function_input hr.1 hzt, hfix z t hzt⟩
  · rintro ⟨hz, rfl⟩
    obtain ⟨t, hzt, _⟩ := hr.1.2 z hz
    exact (hfix z t hzt).symm ▸ hzt

theorem graph_multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {X Y P a1 a2 a3 b1 b2 b3 r1 r2 r3 : M.Carrier .set}
    (ha2 : Endomap X a2) (hb2 : Endomap Y b2) (hr2 : Endomap P r2)
    (ha : CompositionGraph X a1 a2 a3) (hb : CompositionGraph Y b1 b2 b3)
    (hg1 : Graph P a1 b1 r1) (hg2 : Graph P a2 b2 r2) (hg3 : Graph P a3 b3 r3) :
    CompositionGraph P r1 r2 r3 := by
  intro z t
  constructor
  · intro hzt
    obtain ⟨hzP, x, y, u, v, hz, hxu, hyv, ht⟩ := (hg3 z t).mp hzt
    obtain ⟨_, p, hxp, hpu⟩ := (ha x u).mp hxu
    obtain ⟨_, q, hyq, hqv⟩ := (hb y v).mp hyv
    obtain ⟨w, hw⟩ := KuratowskiZF.exists_code hM p q
    have hzw := (hg2 z w).mpr ⟨hzP, x, y, p, q, hz, hxp, hyq, hw⟩
    exact ⟨hzP, w, hzw, (hg1 w t).mpr ⟨hr2.2 z w hzw, p, q, u, v, hw, hpu, hqv, ht⟩⟩
  · rintro ⟨hzP, w, hzw, hwt⟩
    obtain ⟨_, x, y, p, q, hz, hxp, hyq, hw⟩ := (hg2 z w).mp hzw
    obtain ⟨_, p', q', u, v, hw', hpu, hqv, ht⟩ := (hg1 w t).mp hwt
    have hpq := PureKuratowski.code_injective hw hw'
    exact (hg3 z t).mpr ⟨hzP, x, y, u, v, hz,
      (ha x u).mpr ⟨function_input ha2.1 hxp, p, hxp, hpq.1.symm ▸ hpu⟩,
      (hb y v).mpr ⟨function_input hb2.1 hyq, q, hyq, hpq.2.symm ▸ hqv⟩, ht⟩

/-- Literal product order: reverse inclusion on Cohen graphs and source Diagram.le. -/
def Le (D mul z t : M.Carrier .set) : Prop :=
  ∃ p r q s, PureKuratowski.Code M z p r ∧ PureKuratowski.Code M t q s ∧
    (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x q →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x p) ∧ ForcingDiagramOrder.Le D mul r s

def le {m : Nat} (D mul z t : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let p := (Fin.last m).castSucc.castSucc.castSucc
  let r := (Fin.last (m+1)).castSucc.castSucc
  let q := (Fin.last (m+2)).castSucc
  let s := Fin.last (m+3)
  .ex (.ex (.ex (.ex ((PairSyntax.ordered (up z) p r).conj
    ((PairSyntax.ordered (up t) q s).conj
      ((Source.SetLanguage.subset q p).conj (ForcingDiagramOrder.le (up D) (up mul) r s)))))))

theorem le_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul z t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (le D mul z t) ↔
      Le (env D) (env mul) (env z) (env t) := by
  simp only [le, Le, Formula.Realize, KuratowskiZF.source_code,
    ForcingLabelPermutations.subset_semantics (M := M), ForcingDiagramOrder.le_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem le_codes {D mul z t p r q s : M.Carrier .set}
    (hz : PureKuratowski.Code M z p r) (ht : PureKuratowski.Code M t q s) :
    Le D mul z t ↔ (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x q →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x p) ∧ ForcingDiagramOrder.Le D mul r s := by
  constructor
  · rintro ⟨p', r', q', s', hz', ht', hsub, hle⟩
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hz hz'
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective ht ht'
    exact ⟨hsub, hle⟩
  · rintro ⟨hsub, hle⟩
    exact ⟨p, r, q, s, hz, ht, hsub, hle⟩

def OrderPreserving (D mul r : M.Carrier .set) : Prop :=
  ∀ z t Z T, PureKuratowski.PairMember M z Z r → PureKuratowski.PairMember M t T r →
    (Le D mul z t ↔ Le D mul Z T)

def orderPreserving {m : Nat} (D mul r : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let z := (Fin.last m).castSucc.castSucc.castSucc
  let t := (Fin.last (m+1)).castSucc.castSucc
  let Z := (Fin.last (m+2)).castSucc
  let T := Fin.last (m+3)
  .all (.all (.all (.all ((Source.SetLanguage.edge (up r) z Z).imp
    ((Source.SetLanguage.edge (up r) t T).imp ((le (up D) (up mul) z t).iff (le (up D) (up mul) Z T)))))))

theorem orderPreserving_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (orderPreserving D mul r) ↔
      OrderPreserving (env D) (env mul) (env r) := by
  simp only [orderPreserving, OrderPreserving, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    le_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z t Z T hz ht => ⟨(h z t Z T hz ht).1, (h z t Z T hz ht).2⟩,
    fun h z t Z T hz ht => ⟨(h z t Z T hz ht).mp, (h z t Z T hz ht).mpr⟩⟩

theorem graph_order {D mul P a b r : M.Carrier .set}
    (ha : ForcingCohenOrderAction.OrderPreserving a)
    (hb : ForcingDiagramOrder.OrderPreserving D mul b) (hg : Graph P a b r) : OrderPreserving D mul r := by
  intro z t Z T hz ht
  obtain ⟨_, p, q, p', q', hz, hpp, hqq, hZ⟩ := (hg z Z).mp hz
  obtain ⟨_, s, v, s', v', ht, hss, hvv, hT⟩ := (hg t T).mp ht
  rw [le_codes hz ht, le_codes hZ hT]
  exact and_congr (ha p s p' s' hpp hss).symm (hb q v q' v' hqq hvv)

theorem exists_order_action (hM : FirstOrder.Theory.Models M nativeZF)
    {X Y a b : M.Carrier .set} (D mul : M.Carrier .set)
    (ha : Permutation X a) (hb : Permutation Y b)
    (hoa : ForcingCohenOrderAction.OrderPreserving a) (hob : ForcingDiagramOrder.OrderPreserving D mul b) :
    ∃ P r, Cartesian X Y P ∧ Permutation P r ∧ Graph P a b r ∧ OrderPreserving D mul r := by
  obtain ⟨P, hP⟩ := ForcingCohenCoordinates.exists_cartesian hM X Y
  obtain ⟨r, hr, hg⟩ := exists_action hM hP ha hb
  exact ⟨P, r, hP, hr, hg, graph_order hoa hob hg⟩

def identitySentence : Source.Sentence :=
  ((endomap (2 : Fin 6) 5).imp ((identityGraph (0 : Fin 6) 3).imp ((identityGraph (1 : Fin 6) 4).imp ((graph (2 : Fin 6) 3 4 5).imp ((identityGraph (2 : Fin 6) 5)))))).close

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2 h3
  apply (identityGraph_semantics (M := M) env 2 5).mpr
  exact graph_identity hM
    ((endomap_semantics (M := M) env 2 5).mp h0)
    ((identityGraph_semantics (M := M) env 0 3).mp h1)
    ((identityGraph_semantics (M := M) env 1 4).mp h2)
    ((graph_semantics (M := M) env 2 3 4 5).mp h3)

theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)

def multiplicationSentence : Source.Sentence :=
  ((endomap (0 : Fin 12) 4).imp ((endomap (1 : Fin 12) 7).imp ((endomap (2 : Fin 12) 10).imp ((compositionGraph (0 : Fin 12) 3 4 5).imp ((compositionGraph (1 : Fin 12) 6 7 8).imp ((graph (2 : Fin 12) 3 6 9).imp ((graph (2 : Fin 12) 4 7 10).imp ((graph (2 : Fin 12) 5 8 11).imp ((compositionGraph (2 : Fin 12) 9 10 11)))))))))).close

theorem multiplication_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence multiplicationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2 h3 h4 h5 h6 h7
  apply (compositionGraph_semantics (M := M) env 2 9 10 11).mpr
  exact graph_multiplication hM
    ((endomap_semantics (M := M) env 0 4).mp h0)
    ((endomap_semantics (M := M) env 1 7).mp h1)
    ((endomap_semantics (M := M) env 2 10).mp h2)
    ((compositionGraph_semantics (M := M) env 0 3 4 5).mp h3)
    ((compositionGraph_semantics (M := M) env 1 6 7 8).mp h4)
    ((graph_semantics (M := M) env 2 3 6 9).mp h5)
    ((graph_semantics (M := M) env 2 4 7 10).mp h6)
    ((graph_semantics (M := M) env 2 5 8 11).mp h7)

theorem multiplication_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence multiplicationSentence) :=
  ModelTransfer.derives (fun _ hM => multiplication_models hM)

def constructionSentence : Source.Sentence :=
  ((permutation (0 : Fin 6) 4).imp ((permutation 1 5).imp
    ((ForcingCohenOrderAction.orderPreserving 4).imp ((ForcingDiagramOrder.orderPreserving 2 3 5).imp
      (.ex (.ex ((cartesian (0 : Fin 6).castSucc.castSucc (1 : Fin 6).castSucc.castSucc (Fin.last 6).castSucc).conj
        ((permutation (Fin.last 6).castSucc (Fin.last 7)).conj
          ((graph (Fin.last 6).castSucc (4 : Fin 6).castSucc.castSucc (5 : Fin 6).castSucc.castSucc (Fin.last 7)).conj
            (orderPreserving (2 : Fin 6).castSucc.castSucc (3 : Fin 6).castSucc.castSucc (Fin.last 7))))))))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env ha hb hoa hob
  obtain ⟨P, r, hP, hr, hg, ho⟩ := exists_order_action hM (env 2) (env 3)
    ((permutation_semantics (M := M) env 0 4).mp ha) ((permutation_semantics (M := M) env 1 5).mp hb)
    ((ForcingCohenOrderAction.orderPreserving_semantics (M := M) env 4).mp hoa)
    ((ForcingDiagramOrder.orderPreserving_semantics (M := M) env 2 3 5).mp hob)
  let v : Fin 8 → M.Carrier .set := Fin.lastCases r (Fin.lastCases P env)
  refine ⟨P, r, ?_, ?_, ?_, ?_⟩
  · apply (cartesian_semantics (M := M) v (0 : Fin 6).castSucc.castSucc (1 : Fin 6).castSucc.castSucc (Fin.last 6).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hP
  · apply (permutation_semantics (M := M) v (Fin.last 6).castSucc (Fin.last 7)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hr
  · apply (graph_semantics (M := M) v (Fin.last 6).castSucc (4 : Fin 6).castSucc.castSucc (5 : Fin 6).castSucc.castSucc (Fin.last 7)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hg
  · apply (orderPreserving_semantics (M := M) v (2 : Fin 6).castSucc.castSucc (3 : Fin 6).castSucc.castSucc (Fin.last 7)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ho

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

/-- Assemble the actual source Cohen/diagram product from the label permutation.
No component carrier, condition action, or order-invariance result is assumed. -/
theorem exists_source_action (hM : FirstOrder.Theory.Models M nativeZF)
    (D I K B w mul : M.Carrier .set) {pi : M.Carrier .set} (hp : Permutation I pi) :
    ∃ C S X Y P f g a b r,
      Cartesian I K C ∧ Cartesian C B S ∧ ForcingCohenConditions.Carrier S w X ∧
      ForcingDiagramCarrier.Carrier D I Y ∧ Cartesian X Y P ∧
      Permutation C f ∧ ForcingCohenCoordinates.Graph C pi f ∧
      Permutation S g ∧ ForcingCohenCoordinates.Graph S f g ∧
      Permutation X a ∧ ForcingCohenOrderAction.ActionGraph X g a ∧
      Permutation Y b ∧ ForcingDiagramCarrier.Graph D Y pi b ∧
      Permutation P r ∧ Graph P a b r ∧ OrderPreserving D mul r := by
  obtain ⟨C, S, X, f, g, a, hC, hS, hX, hf, hfg, hg, hgg, ha, hga, hoa⟩ :=
    ForcingCohenOrderAction.exists_system hM I K B w hp
  obtain ⟨Y, b, hY, hb, hgb, hob⟩ := ForcingDiagramOrder.exists_order_action hM D I mul hp
  obtain ⟨P, r, hP, hr, hgr, hor⟩ := exists_order_action hM D mul ha hb hoa hob
  exact ⟨C, S, X, Y, P, f, g, a, b, r, hC, hS, hX, hY, hP,
    hf, hfg, hg, hgg, ha, hga, hb, hgb, hr, hgr, hor⟩

def assemblySentence : Source.Sentence :=
  ((permutation (1 : Fin 7) 6).imp (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex ((cartesian (1 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (2 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (
    (cartesian (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (3 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (
    (ForcingCohenConditions.carrier (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (4 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (
    (ForcingDiagramCarrier.carrier (0 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (1 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj (
    (cartesian (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc).conj (
    (permutation (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 12).castSucc.castSucc.castSucc.castSucc).conj (
    (ForcingCohenCoordinates.graph (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (6 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 12).castSucc.castSucc.castSucc.castSucc).conj (
    (permutation (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 13).castSucc.castSucc.castSucc).conj (
    (ForcingCohenCoordinates.graph (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 12).castSucc.castSucc.castSucc.castSucc (Fin.last 13).castSucc.castSucc.castSucc).conj (
    (permutation (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 14).castSucc.castSucc).conj (
    (ForcingCohenOrderAction.actionGraph (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 13).castSucc.castSucc.castSucc (Fin.last 14).castSucc.castSucc).conj (
    (permutation (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 15).castSucc).conj (
    (ForcingDiagramCarrier.graph (0 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (6 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 15).castSucc).conj (
    (permutation (Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 16)).conj (
    (graph (Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 14).castSucc.castSucc (Fin.last 15).castSucc (Fin.last 16)).conj (
    (orderPreserving (0 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (5 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 16))))))))))))))))))))))))))))).close

theorem assembly_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence assemblySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp
  obtain ⟨C, S, X, Y, P, f, g, a, b, r, hC, hS, hX, hY, hP,
      hf, hfg, hg, hgg, ha, hga, hb, hgb, hr, hgr, hor⟩ :=
    exists_source_action hM (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)
      ((permutation_semantics (M := M) env 1 6).mp hp)
  let v : Fin 17 → M.Carrier .set := Fin.lastCases r (Fin.lastCases b (Fin.lastCases a
    (Fin.lastCases g (Fin.lastCases f (Fin.lastCases P (Fin.lastCases Y
      (Fin.lastCases X (Fin.lastCases S (Fin.lastCases C env)))))))))
  refine ⟨C, S, X, Y, P, f, g, a, b, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (cartesian_semantics (M := M) v (1 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (2 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hC
  · apply (cartesian_semantics (M := M) v (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (3 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hS
  · apply (ForcingCohenConditions.carrier_semantics (M := M) v (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (4 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hX
  · apply (ForcingDiagramCarrier.carrier_semantics (M := M) v (0 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (1 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hY
  · apply (cartesian_semantics (M := M) v (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hP
  · apply (permutation_semantics (M := M) v (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 12).castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hf
  · apply (ForcingCohenCoordinates.graph_semantics (M := M) v (Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (6 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 12).castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hfg
  · apply (permutation_semantics (M := M) v (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 13).castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hg
  · apply (ForcingCohenCoordinates.graph_semantics (M := M) v (Fin.last 8).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 12).castSucc.castSucc.castSucc.castSucc (Fin.last 13).castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hgg
  · apply (permutation_semantics (M := M) v (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 14).castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ha
  · apply (ForcingCohenOrderAction.actionGraph_semantics (M := M) v (Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 13).castSucc.castSucc.castSucc (Fin.last 14).castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hga
  · apply (permutation_semantics (M := M) v (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 15).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hb
  · apply (ForcingDiagramCarrier.graph_semantics (M := M) v (0 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (6 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 15).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hgb
  · apply (permutation_semantics (M := M) v (Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 16)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hr
  · apply (graph_semantics (M := M) v (Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 14).castSucc.castSucc (Fin.last 15).castSucc (Fin.last 16)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hgr
  · apply (orderPreserving_semantics (M := M) v (0 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (5 : Fin 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 16)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hor

theorem assembly_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence assemblySentence) :=
  ModelTransfer.derives (fun _ hM => assembly_models hM)

end PPAC.Migration.ForcingProductAction
