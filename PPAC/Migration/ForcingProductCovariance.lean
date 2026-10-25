/- The actual fixed-carrier ProductNames action supplies the algebraic
Family/Covariance context consumed by HS.smul. Conjugation and inverse laws
are derived from the already proved identity/composition of that same action. -/
import PPAC.Migration.ForcingProductFamily
import PPAC.Migration.ForcingSupportFilter
import PPAC.Migration.ForcingHSAction

namespace PPAC.Migration.ForcingProductCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingProductFamily (Presentation presentation presentation_semantics Action action action_semantics actionFormula)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem label_left_inverse {I pi inv e : M.Carrier .set} (hp : Permutation I pi)
    (hi : InverseGraph pi inv) (he : IdentityGraph I e) : CompositionGraph I inv pi e := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx, rfl⟩ := (he x z).mp hxz
    obtain ⟨y, hxy, _⟩ := hp.1.1.2 x hx
    exact ⟨hx, y, hxy, (hi x y).mp hxy⟩
  · rintro ⟨hx, y, hxy, hyz⟩
    exact (he x z).mpr ⟨hx, hp.2.1 x z y hxy ((hi z y).mpr hyz)⟩

theorem inverse (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi inv r i : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (hpi : Permutation I pi) (hpii : InverseGraph pi inv)
    (hA : Action D C S X Y P W pi r) (hB : Action D C S X Y P W inv i) : InverseGraph r i := by
  have hr := ForcingProductFamily.action_permutation hA
  have hi := ForcingProductFamily.action_permutation hB
  obtain ⟨e, he, hie⟩ := exists_identity hM I
  obtain ⟨ae, hAe⟩ := ForcingProductFamily.exists_action hM hp he
  have hiae := ForcingProductFamily.identity hM hp hie hAe
  have hcomp := ForcingProductFamily.multiplication hM hp hpi (label_left_inverse hpi hpii hie) hB hA hAe
  have hforward : ∀ x y, PureKuratowski.PairMember M x y r → PureKuratowski.PairMember M y x i := by
    intro x y hxy
    obtain ⟨z, hyz, _⟩ := hi.1.1.2 y (hr.1.2 x y hxy)
    have hxz := ((hiae x z).mp ((hcomp x z).mpr ⟨function_input hr.1.1 hxy, y, hxy, hyz⟩)).2
    exact hxz.symm ▸ hyz
  intro x y
  constructor
  · exact hforward x y
  · intro hyx
    obtain ⟨z, hxz, _⟩ := hr.1.1.2 x (hi.1.2 y x hyx)
    exact hi.2.1 z y x (hforward x z hxz) hyx ▸ hxz

theorem conjugacy (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi inv g h r i s t : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (hinv : Permutation I inv) (hg : Permutation I g)
    (hconj : ForcingNameConjugacy.Conjugate I pi inv g h)
    (hA : Action D C S X Y P W pi r) (hB : Action D C S X Y P W inv i)
    (hG : Action D C S X Y P W g s) (hH : Action D C S X Y P W h t) :
    ForcingNameConjugacy.Conjugate W r i s t := by
  obtain ⟨mid, hmid, hgi, hpm⟩ := hconj
  obtain ⟨mid', hm', hgi'⟩ := exists_composition hM hg hinv
  have hmEq : mid = mid' := ForcingConjugationGraph.endomap_ext hM hmid hm'.1
    (fun x y => (hgi x y).trans (hgi' x y).symm)
  have hm : Permutation I mid := hmEq.symm ▸ hm'
  obtain ⟨a, ha⟩ := ForcingProductFamily.exists_action hM hp hm
  exact ⟨a, (ForcingProductFamily.action_permutation ha).1,
    ForcingProductFamily.multiplication hM hp hinv hgi hG hB ha,
    ForcingProductFamily.multiplication hM hp hm hpm hA ha hH⟩

theorem covariance (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G pi inv c r i : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hinv : Permutation I inv)
    (hc : ForcingConjugationGraph.Graph I G pi inv c)
    (hA : Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi r)
    (hB : Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) inv i) :
    ForcingStabilizerTransport.Covariance actionFormula v G (v 6) c r i := by
  intro g h s t hg _ hgh hgs hht
  exact conjugacy hM hp hinv ((hG g).mp hg) ((hc g h).mp hgh).2.2 hA hB
    ((ForcingProductFamily.mapRel_action v g s).mp hgs) ((ForcingProductFamily.mapRel_action v h t).mp hht)

theorem context (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F mu pi inv c r i : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hpi : Permutation I pi) (hinv : Permutation I inv)
    (hpii : InverseGraph pi inv) (hcc : Permutation G c) (hc : ForcingConjugationGraph.Graph I G pi inv c)
    (hA : Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi r)
    (hB : Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) inv i)
    (hF : ForcingSupportFilter.Filter I G mu F) :
    ForcingStabilizerTransport.Context actionFormula v G (v 6) F c r i :=
  ⟨ForcingProductFamily.family hM v hp hG, hcc, ForcingProductFamily.action_permutation hA,
    (ForcingProductFamily.action_permutation hB).1, inverse hM hp hpi hpii hA hB,
    covariance hM v hp hG hinv hc hA hB,
    ForcingSupportFilter.normal_image hM hG hF hpi hinv.1 hpii hcc hc⟩

/-- Concrete data of ProductNames.system, with the already constructed small-support filter.
No normal-image or HS-closure premise is included. -/
def SystemData (v : Fin 7 → M.Carrier .set) (I K B w G F mu pi inv c r i : M.Carrier .set) : Prop :=
  Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) ∧
  ForcingLabelPermutations.Carrier I G ∧ Permutation I pi ∧ Permutation I inv ∧
  InverseGraph pi inv ∧ Permutation G c ∧ ForcingConjugationGraph.Graph I G pi inv c ∧
  Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi r ∧
  Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) inv i ∧
  ForcingSupportFilter.Filter I G mu F

/-- All fields are constructed from the fixed presentation and one label permutation. -/
theorem exists_data (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w mu pi : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hpi : Permutation I pi) : ∃ G F inv c r i, SystemData v I K B w G F mu pi inv c r i := by
  obtain ⟨G, hG⟩ := ForcingLabelPermutations.exists_carrier hM I
  obtain ⟨F, hF⟩ := ForcingSupportFilter.exists_filter hM I G mu
  obtain ⟨inv, hi, hpii⟩ := exists_inverse hM hpi
  obtain ⟨c, hc, hcg⟩ := ForcingConjugationGraph.exists_graph hM hG hpi hi hpii
  obtain ⟨r, hr⟩ := ForcingProductFamily.exists_action hM hp hpi
  obtain ⟨i, hiA⟩ := ForcingProductFamily.exists_action hM hp hi
  exact ⟨G, F, inv, c, r, i, hp, hG, hpi, hi, hpii, hc, hcg, hr, hiA, hF⟩

def systemData {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i : Fin m) : Formula m :=
  (presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).conj (
  (ForcingLabelPermutations.carrier I G).conj ((permutation I pi).conj ((permutation I inv).conj (
  (inverseGraph pi inv).conj ((permutation G c).conj ((ForcingConjugationGraph.graph I G pi inv c).conj (
  (action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) pi r).conj (
  (action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) inv i).conj (
  ForcingSupportFilter.filter I G mu F)))))))))

theorem systemData_semantics {m : Nat} (env : Fin m → M.Carrier .set) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c r i : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (systemData rho I K B w G F mu pi inv c r i) ↔
    SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu)
      (env pi) (env inv) (env c) (env r) (env i) := by
  simp only [systemData, SystemData, Formula.Realize, presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M), permutation_semantics (M := M),
    inverseGraph_semantics (M := M), ForcingConjugationGraph.graph_semantics (M := M),
    action_semantics (M := M), ForcingSupportFilter.filter_semantics (M := M)]

theorem context_of_data (hM : FirstOrder.Theory.Models M nativeZF) {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c r i : M.Carrier .set}
    (h : SystemData v I K B w G F mu pi inv c r i) :
    ForcingStabilizerTransport.Context actionFormula v G (v 6) F c r i := by
  obtain ⟨hp, hG, hpi, hinv, hpii, hcc, hc, hA, hB, hF⟩ := h
  exact context hM v hp hG hpi hinv hpii hcc hc hA hB hF

/-- The source HS.smul now has the concrete uniform action and support-defined filter. -/
theorem hs_action (hM : FirstOrder.Theory.Models M nativeZF) {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c r i : M.Carrier .set}
    (h : SystemData v I K B w G F mu pi inv c r i) :
    ∀ sigma, ForcingHS.HS actionFormula v G (v 6) F sigma → ∀ out,
      ForcingStabilizer.Action (v 6) r sigma out → ForcingHS.HS actionFormula v G (v 6) F out :=
  ForcingHSAction.hs_action hM (context_of_data hM h)

def contextSentence {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i : Fin m) : Source.Sentence :=
  ((systemData rho I K B w G F mu pi inv c r i).imp
    (ForcingStabilizerTransport.context actionFormula rho G (rho 6) F c r i)).close

theorem context_models {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (contextSentence rho I K B w G F mu pi inv c r i)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h
  exact (ForcingStabilizerTransport.context_semantics (M := M) env actionFormula rho G (rho 6) F c r i).mpr
    (context_of_data hM ((systemData_semantics env rho I K B w G F mu pi inv c r i).mp h))

theorem context_kernel_certificate {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i : Fin m) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (contextSentence rho I K B w G F mu pi inv c r i)) :=
  ModelTransfer.derives (fun _ hM => context_models rho I K B w G F mu pi inv c r i hM)

def hsSentence {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i sigma : Fin m) : Source.Sentence :=
  ((systemData rho I K B w G F mu pi inv c r i).imp
    (ForcingHSAction.preservesAt actionFormula rho G (rho 6) F r sigma)).close

theorem hs_models {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i sigma : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (hsSentence rho I K B w G F mu pi inv c r i sigma)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h
  exact (ForcingHSAction.preservesAt_semantics (M := M) env actionFormula rho G (rho 6) F r sigma).mpr
    (hs_action hM ((systemData_semantics env rho I K B w G F mu pi inv c r i).mp h) (env sigma))

theorem hs_kernel_certificate {m : Nat} (rho : Fin 7 → Fin m) (I K B w G F mu pi inv c r i sigma : Fin m) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (hsSentence rho I K B w G F mu pi inv c r i sigma)) :=
  ModelTransfer.derives (fun _ hM => hs_models rho I K B w G F mu pi inv c r i sigma hM)

/-- Existential closure of the concrete data, in the original pure-set language. -/
def constructionSentence {m : Nat} (rho : Fin 7 → Fin m) (I K B w mu pi : Fin m) : Source.Sentence :=
  let up : Fin m → Fin (m+6) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  ((presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((permutation I pi).imp (.ex (.ex (.ex (.ex (.ex (.ex (
      systemData (fun j => up (rho j)) (up I) (up K) (up B) (up w)
        (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
        (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (up mu) (up pi)
        (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc
        (Fin.last (m+4)).castSucc (Fin.last (m+5))))))))))).close

theorem construction_models {m : Nat} (rho : Fin 7 → Fin m) (I K B w mu pi : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w mu pi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hpi
  obtain ⟨G,F,inv,c,r,i,h⟩ := exists_data hM (fun j => env (rho j)) (mu := env mu)
    ((presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((permutation_semantics (M := M) env I pi).mp hpi)
  let v : Fin (m+6) → M.Carrier .set := Fin.lastCases i (Fin.lastCases r (Fin.lastCases c
    (Fin.lastCases inv (Fin.lastCases F (Fin.lastCases G env)))))
  let up : Fin m → Fin (m+6) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  refine ⟨G,F,inv,c,r,i,?_⟩
  apply (systemData_semantics (M := M) v (fun j => up (rho j)) (up I) (up K) (up B) (up w)
    (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (up mu) (up pi)
    (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc
    (Fin.last (m+4)).castSucc (Fin.last (m+5))).mpr
  simpa only [v, up, Fin.lastCases_last, Fin.lastCases_castSucc] using h

theorem construction_kernel_certificate {m : Nat} (rho : Fin 7 → Fin m) (I K B w mu pi : Fin m) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho I K B w mu pi)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w mu pi hM)

end PPAC.Migration.ForcingProductCovariance

