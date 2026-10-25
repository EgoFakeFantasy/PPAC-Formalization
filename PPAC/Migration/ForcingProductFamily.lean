/- Pinned ProductNames.actionHom on fixed, internally constructed carriers.
One formula describes the entire label-to-condition action through the exact
Cohen, diagram, product and WithTop graphs. No host-selected action function. -/
import PPAC.Migration.ForcingWithTopAction
import PPAC.Migration.ForcingConjugationGraph

namespace PPAC.Migration.ForcingProductFamily
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Presentation (D I K B w C S X Y P W : M.Carrier .set) : Prop :=
  ForcingCohenCoordinates.Cartesian I K C ∧ ForcingCohenCoordinates.Cartesian C B S ∧
    ForcingCohenConditions.Carrier S w X ∧ ForcingDiagramCarrier.Carrier D I Y ∧
    ForcingCohenCoordinates.Cartesian X Y P ∧ ForcingWithTopCarrier.Carrier P W

def presentation {m : Nat} (D I K B w C S X Y P W : Fin m) : Formula m :=
  (ForcingCohenCoordinates.cartesian I K C).conj ((ForcingCohenCoordinates.cartesian C B S).conj
    ((ForcingCohenConditions.carrier S w X).conj ((ForcingDiagramCarrier.carrier D I Y).conj
      ((ForcingCohenCoordinates.cartesian X Y P).conj (ForcingWithTopCarrier.carrier P W)))))

theorem presentation_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D I K B w C S X Y P W : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (presentation D I K B w C S X Y P W) ↔
      Presentation (env D) (env I) (env K) (env B) (env w) (env C) (env S) (env X) (env Y) (env P) (env W) := by
  simp only [presentation, Presentation, Formula.Realize, ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingCohenConditions.carrier_semantics (M := M), ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingWithTopCarrier.carrier_semantics (M := M)]

theorem exists_presentation (hM : FirstOrder.Theory.Models M nativeZF) (D I K B w : M.Carrier .set) :
    ∃ C S X Y P W, Presentation D I K B w C S X Y P W := by
  obtain ⟨C, hC⟩ := ForcingCohenCoordinates.exists_cartesian hM I K
  obtain ⟨S, hS⟩ := ForcingCohenCoordinates.exists_cartesian hM C B
  obtain ⟨X, hX⟩ := ForcingCohenConditions.exists_carrier hM S w
  obtain ⟨Y, hY⟩ := ForcingDiagramCarrier.exists_carrier hM D I
  obtain ⟨P, hP⟩ := ForcingCohenCoordinates.exists_cartesian hM X Y
  obtain ⟨W, hW⟩ := ForcingWithTopCarrier.exists_carrier hM P
  exact ⟨C, S, X, Y, P, W, hC, hS, hX, hY, hP, hW⟩

def Action (D C S X Y P W pi a : M.Carrier .set) : Prop :=
  ∃ f g ac ad r, Permutation C f ∧ ForcingCohenCoordinates.Graph C pi f ∧
    Permutation S g ∧ ForcingCohenCoordinates.Graph S f g ∧
    Permutation X ac ∧ ForcingCohenOrderAction.ActionGraph X g ac ∧
    Permutation Y ad ∧ ForcingDiagramCarrier.Graph D Y pi ad ∧
    Permutation P r ∧ ForcingProductAction.Graph P ac ad r ∧
    Permutation W a ∧ ForcingWithTopAction.Graph W r a

def action {m : Nat} (D C S X Y P W pi a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let f := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let g := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let ac := (Fin.last (m+2)).castSucc.castSucc
  let ad := (Fin.last (m+3)).castSucc
  let r := (Fin.last (m+4))
  .ex (.ex (.ex (.ex (.ex ((permutation (up C) f).conj (
    (ForcingCohenCoordinates.graph (up C) (up pi) f).conj (
    (permutation (up S) g).conj (
    (ForcingCohenCoordinates.graph (up S) f g).conj (
    (permutation (up X) ac).conj (
    (ForcingCohenOrderAction.actionGraph (up X) g ac).conj (
    (permutation (up Y) ad).conj (
    (ForcingDiagramCarrier.graph (up D) (up Y) (up pi) ad).conj (
    (permutation (up P) r).conj (
    (ForcingProductAction.graph (up P) ac ad r).conj (
    (permutation (up W) (up a)).conj (
    (ForcingWithTopAction.graph (up W) r (up a))))))))))))))))))

theorem action_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D C S X Y P W pi a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (action D C S X Y P W pi a) ↔
      Action (env D) (env C) (env S) (env X) (env Y) (env P) (env W) (env pi) (env a) := by
  simp only [action, Action, Formula.Realize, permutation_semantics (M := M),
    ForcingCohenCoordinates.graph_semantics (M := M), ForcingCohenOrderAction.actionGraph_semantics (M := M),
    ForcingDiagramCarrier.graph_semantics (M := M), ForcingProductAction.graph_semantics (M := M),
    ForcingWithTopAction.graph_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (hpi : Permutation I pi) :
    ∃ a, Action D C S X Y P W pi a := by
  obtain ⟨hC, hS, hX, hY, hP, hW⟩ := hp
  obtain ⟨f, hf, hfg⟩ := ForcingCohenCoordinates.exists_lift hM hC hpi
  obtain ⟨g, hg, hgg⟩ := ForcingCohenCoordinates.exists_lift hM hS hf
  obtain ⟨ac, hac, hacg⟩ := ForcingCohenOrderAction.exists_action hM hS hX hf hg hgg
  obtain ⟨ad, had, hadg⟩ := ForcingDiagramCarrier.exists_graph hM hY hpi
  obtain ⟨r, hr, hrg⟩ := ForcingProductAction.exists_action hM hP hac had
  obtain ⟨a, ha, hag⟩ := ForcingWithTopAction.exists_action hM hW hr
  exact ⟨a, f, g, ac, ad, r, hf, hfg, hg, hgg, hac, hacg, had, hadg, hr, hrg, ha, hag⟩

theorem action_permutation {D C S X Y P W pi a : M.Carrier .set}
    (h : Action D C S X Y P W pi a) : Permutation W a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := h
  exact ha

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {D C S X Y P W pi a b : M.Carrier .set}
    (ha : Action D C S X Y P W pi a) (hb : Action D C S X Y P W pi b) : a = b := by
  obtain ⟨f, g, ac, ad, r, hf, hfg, hg, hgg, hac, hacg, had, hadg, hr, hrg, ha, hag⟩ := ha
  obtain ⟨f', g', ac', ad', r', hf', hfg', hg', hgg', hac', hacg', had', hadg', hr', hrg', hb, hbg⟩ := hb
  have ef : f = f' := ForcingConjugationGraph.endomap_ext hM hf.1 hf'.1
    (fun x y => (hfg x y).trans (hfg' x y).symm)
  subst f'
  have eg : g = g' := ForcingConjugationGraph.endomap_ext hM hg.1 hg'.1
    (fun x y => (hgg x y).trans (hgg' x y).symm)
  subst g'
  have ec : ac = ac' := ForcingConjugationGraph.endomap_ext hM hac.1 hac'.1
    (fun x y => (hacg x y).trans (hacg' x y).symm)
  subst ac'
  have ed : ad = ad' := ForcingConjugationGraph.endomap_ext hM had.1 had'.1
    (fun x y => (hadg x y).trans (hadg' x y).symm)
  subst ad'
  have er : r = r' := ForcingConjugationGraph.endomap_ext hM hr.1 hr'.1
    (fun x y => (hrg x y).trans (hrg' x y).symm)
  subst r'
  exact ForcingConjugationGraph.endomap_ext hM ha.1 hb.1
    (fun x y => (hag x y).trans (hbg x y).symm)

theorem identity (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W e a : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (he : IdentityGraph I e)
    (h : Action D C S X Y P W e a) : IdentityGraph W a := by
  obtain ⟨_, _, hX, hY, _, _⟩ := hp
  obtain ⟨f, g, ac, ad, r, hf, hfg, hg, hgg, hac, hacg, had, hadg, hr, hrg, ha, hag⟩ := h
  have hc := ForcingCohenActionLaws.permute_one hM hX hf.1 hg.1 hac.1 he hfg hgg hacg
  have hd := ForcingDiagramCarrier.graph_identity hM hY had.1 he hadg
  have hrid := ForcingProductAction.graph_identity hM hr.1 hc hd hrg
  exact ForcingWithTopAction.graph_identity hM ha.1 hrid hag

theorem multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi sigma product a b c : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (hs : Permutation I sigma)
    (hprod : CompositionGraph I pi sigma product)
    (hA : Action D C S X Y P W pi a) (hB : Action D C S X Y P W sigma b)
    (hC : Action D C S X Y P W product c) : CompositionGraph W a b c := by
  obtain ⟨_, _, hX, hY, _, _⟩ := hp
  obtain ⟨f1, g1, c1, d1, r1, hf1, hfg1, hg1, hgg1, hc1, hcg1, hd1, hdg1, hr1, hrg1, ha, hag⟩ := hA
  obtain ⟨f2, g2, c2, d2, r2, hf2, hfg2, hg2, hgg2, hc2, hcg2, hd2, hdg2, hr2, hrg2, hb, hbg⟩ := hB
  obtain ⟨f3, g3, c3, d3, r3, hf3, hfg3, hg3, hgg3, hc3, hcg3, hd3, hdg3, hr3, hrg3, hc, hgc⟩ := hC
  have hcc := ForcingCohenActionLaws.permute_mul hM hX hs.1 hf2.1 hg2.1 hc1.1 hc2.1 hprod
    hfg1 hfg2 hfg3 hgg1 hgg2 hgg3 hcg1 hcg2 hcg3
  have hdd := ForcingDiagramCarrier.graph_multiplication hM hY hd1.1 hd2.1 hd3.1 hprod hdg1 hdg2 hdg3
  have hrr := ForcingProductAction.graph_multiplication hM hc2.1 hd2.1 hr2.1 hcc hdd hrg1 hrg2 hrg3
  exact ForcingWithTopAction.graph_multiplication hM hr2.1 hb.1 hrr hag hbg hgc

theorem order (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi a : M.Carrier .set} (mul : M.Carrier .set)
    (hp : Presentation D I K B w C S X Y P W) (hpi : Permutation I pi)
    (h : Action D C S X Y P W pi a) : ForcingWithTopAction.OrderPreserving D mul a := by
  obtain ⟨_, _, hX, hY, _, _⟩ := hp
  obtain ⟨f, g, ac, ad, r, _, _, hg, _, _, hacg, _, hadg, _, hrg, _, hag⟩ := h
  exact ForcingWithTopAction.graph_order
    (ForcingProductAction.graph_order (ForcingCohenOrderAction.graph_order hX hg hacg)
      (ForcingDiagramOrder.graph_order hM hY hpi hadg) hrg) hag

theorem top_fixed {D I K B w C S X Y P W pi a e : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (he : ForcingWithTopCarrier.Empty e)
    (h : Action D C S X Y P W pi a) : PureKuratowski.PairMember M e e a := by
  obtain ⟨_, _, _, _, _, hW⟩ := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hag⟩ := h
  exact ForcingWithTopAction.top_fixed hW hag he

/-- Seven fixed parameters D,C,S,X,Y,P,W followed by input pi and output a. -/
def actionFormula : Formula 9 :=
  action (0 : Fin 7).castSucc.castSucc (1 : Fin 7).castSucc.castSucc (2 : Fin 7).castSucc.castSucc
    (3 : Fin 7).castSucc.castSucc (4 : Fin 7).castSucc.castSucc (5 : Fin 7).castSucc.castSucc
    (6 : Fin 7).castSucc.castSucc (Fin.last 7).castSucc (Fin.last 8)

theorem mapRel_action (v : Fin 7 → M.Carrier .set) (pi a : M.Carrier .set) :
    ForcingMapConditions.MapRel actionFormula v pi a ↔ Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi a := by
  unfold ForcingMapConditions.MapRel actionFormula
  rw [action_semantics]
  rfl

theorem family (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) : ForcingStabilizerTransport.Family actionFormula v G (v 6) := by
  constructor
  · intro pi hpi
    obtain ⟨a, ha⟩ := exists_action hM hp ((hG pi).mp hpi)
    exact ⟨a, (mapRel_action v pi a).mpr ha⟩
  · intro pi a _ ha
    exact action_permutation ((mapRel_action v pi a).mp ha)

def uniqueSentence : Source.Sentence :=
  ((action (0 : Fin 10) 1 2 3 4 5 6 7 8).imp ((action (0 : Fin 10) 1 2 3 4 5 6 7 9).imp ((Formula.equal (8 : Fin 10) 9)))).close

theorem unique_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniqueSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1
  exact unique hM
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 7 8).mp h0)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 7 9).mp h1)

theorem unique_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  ModelTransfer.derives (fun _ hM => unique_models hM)

def identitySentence : Source.Sentence :=
  ((presentation (0 : Fin 13) 7 8 9 10 1 2 3 4 5 6).imp ((identityGraph (7 : Fin 13) 11).imp ((action (0 : Fin 13) 1 2 3 4 5 6 11 12).imp ((identityGraph (6 : Fin 13) 12))))).close

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2
  apply (identityGraph_semantics (M := M) env 6 12).mpr
  exact identity hM
    ((presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp h0)
    ((identityGraph_semantics (M := M) env 7 11).mp h1)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 11 12).mp h2)

theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)

def multiplicationSentence : Source.Sentence :=
  ((presentation (0 : Fin 17) 7 8 9 10 1 2 3 4 5 6).imp ((permutation (7 : Fin 17) 12).imp ((compositionGraph (7 : Fin 17) 11 12 13).imp ((action (0 : Fin 17) 1 2 3 4 5 6 11 14).imp ((action (0 : Fin 17) 1 2 3 4 5 6 12 15).imp ((action (0 : Fin 17) 1 2 3 4 5 6 13 16).imp ((compositionGraph (6 : Fin 17) 14 15 16)))))))).close

theorem multiplication_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence multiplicationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2 h3 h4 h5
  apply (compositionGraph_semantics (M := M) env 6 14 15 16).mpr
  exact multiplication hM
    ((presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp h0)
    ((permutation_semantics (M := M) env 7 12).mp h1)
    ((compositionGraph_semantics (M := M) env 7 11 12 13).mp h2)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 11 14).mp h3)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 12 15).mp h4)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 13 16).mp h5)

theorem multiplication_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence multiplicationSentence) :=
  ModelTransfer.derives (fun _ hM => multiplication_models hM)

def orderSentence : Source.Sentence :=
  ((presentation (0 : Fin 14) 7 8 9 10 1 2 3 4 5 6).imp ((permutation (7 : Fin 14) 12).imp ((action (0 : Fin 14) 1 2 3 4 5 6 12 13).imp ((ForcingWithTopAction.orderPreserving (0 : Fin 14) 11 13))))).close

theorem order_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence orderSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2
  apply (ForcingWithTopAction.orderPreserving_semantics (M := M) env 0 11 13).mpr
  exact order hM (env 11)
    ((presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp h0)
    ((permutation_semantics (M := M) env 7 12).mp h1)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 12 13).mp h2)

theorem order_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence orderSentence) :=
  ModelTransfer.derives (fun _ hM => order_models hM)

def topSentence : Source.Sentence :=
  ((presentation (0 : Fin 14) 7 8 9 10 1 2 3 4 5 6).imp ((ForcingWithTopCarrier.empty (13 : Fin 14)).imp ((action (0 : Fin 14) 1 2 3 4 5 6 11 12).imp ((Source.SetLanguage.edge (12 : Fin 14) 13 13))))).close

theorem top_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence topSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2
  apply (KuratowskiZF.source_edge (M := M) env 12 13 13).mpr
  exact top_fixed
    ((presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp h0)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env 13).mp h1)
    ((action_semantics (M := M) env 0 1 2 3 4 5 6 11 12).mp h2)

theorem top_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence topSentence) :=
  ModelTransfer.derives (fun _ hM => top_models hM)

def constructionBody : Formula 5 :=
  let rho : Fin 7 → Fin 12 := Fin.cases (0 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 6).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 7).castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 8).castSucc.castSucc.castSucc ((Source.SetLanguage.args2 (Fin.last 9).castSucc.castSucc (Fin.last 10).castSucc))))))
  (Formula.ex (.ex (.ex (.ex (.ex (.ex (.ex ((presentation (0 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (1 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (2 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (3 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (4 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 6).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 7).castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc.castSucc (Fin.last 9).castSucc.castSucc (Fin.last 10).castSucc).conj ((ForcingLabelPermutations.carrier (1 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 11)).conj (ForcingStabilizerTransport.family actionFormula rho (Fin.last 11) (Fin.last 10).castSucc))))))))))

def constructionSentence : Source.Sentence := constructionBody.close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨C, S, X, Y, P, W, hp⟩ := exists_presentation hM (env 0) (env 1) (env 2) (env 3) (env 4)
  obtain ⟨G, hG⟩ := ForcingLabelPermutations.exists_carrier hM (env 1)
  let v : Fin 12 → M.Carrier .set := Fin.lastCases G (Fin.lastCases W (Fin.lastCases P
    (Fin.lastCases Y (Fin.lastCases X (Fin.lastCases S (Fin.lastCases C env))))))
  let rho : Fin 7 → Fin 12 := Fin.cases (0 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 6).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 7).castSucc.castSucc.castSucc.castSucc (Fin.cases (Fin.last 8).castSucc.castSucc.castSucc ((Source.SetLanguage.args2 (Fin.last 9).castSucc.castSucc (Fin.last 10).castSucc))))))
  refine ⟨C, S, X, Y, P, W, G, ?_, ?_, ?_⟩
  · apply (presentation_semantics (M := M) v (0 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (1 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (2 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (3 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (4 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 6).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 7).castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc.castSucc (Fin.last 9).castSucc.castSucc (Fin.last 10).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hp
  · apply (ForcingLabelPermutations.carrier_semantics (M := M) v (1 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 11)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hG
  · apply (ForcingStabilizerTransport.family_semantics (M := M) v actionFormula rho (Fin.last 11) (Fin.last 10).castSucc).mpr
    let params : Fin 7 → M.Carrier .set := Fin.cases (env 0) (Fin.cases C
      (Fin.cases S (Fin.cases X (Fin.cases Y (Source.SetLanguage.args2 P W)))))
    have hv : (fun j => v (rho j)) = params := by
      funext j
      cases j using Fin.cases with
      | zero => simp only [v, rho, params, Fin.cases_zero, Fin.lastCases_castSucc]
      | succ j =>
        cases j using Fin.cases with
        | zero => simp only [v, rho, params, Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc]
        | succ j =>
          cases j using Fin.cases with
          | zero => simp only [v, rho, params, Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc]
          | succ j =>
            cases j using Fin.cases with
            | zero => simp only [v, rho, params, Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc]
            | succ j =>
              cases j using Fin.cases with
              | zero => simp only [v, rho, params, Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc]
              | succ j =>
                cases j using Fin.cases with
                | zero => simp only [v, rho, params, Fin.cases_zero, Fin.cases_succ, Source.SetLanguage.args2, Fin.lastCases_last, Fin.lastCases_castSucc]
                | succ j =>
                  cases j using Fin.cases with
                  | zero => simp only [v, rho, params, Fin.cases_zero, Fin.cases_succ, Source.SetLanguage.args2, Source.SetLanguage.args1, Fin.lastCases_last, Fin.lastCases_castSucc]
                  | succ j =>
                    exact Fin.elim0 j
    rw [hv]
    change ForcingStabilizerTransport.Family actionFormula params G W
    have hp' : Presentation (params 0) (env 1) (env 2) (env 3) (env 4)
        (params 1) (params 2) (params 3) (params 4) (params 5) (params 6) := by
      change Presentation (env 0) (env 1) (env 2) (env 3) (env 4) C S X Y P W
      exact hp
    exact family hM params hp' hG

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingProductFamily
