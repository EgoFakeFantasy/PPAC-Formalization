/- Pinned SymmetricNames.collect_HS / collect. Consumers: separate, power,
and replacement witnesses. All hypotheses of the source subgroup/entry
permutation contract are encoded as object formulas; HS closure is proved. -/
import PPAC.Migration.ForcingCollectedName
import PPAC.Migration.ForcingProductStabilizer
import PPAC.Migration.ForcingNormalFilter

namespace PPAC.Migration.ForcingCollectedHS
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingCollectedName (Admissible admissible Collected collected)
open ForcingStabilizer (Action action)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ReplacementPredicates (paramsUp rel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def familyHS {m : Nat} (rho : Fin 7 → Fin m) (G P F J f : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc J.castSucc.castSucc).imp
    ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (ForcingHS.hs actionFormula (paramsUp (paramsUp rho)) G.castSucc.castSucc
        P.castSucc.castSucc F.castSucc.castSucc (Fin.last (m+1))))))

def FamilyHS (v : Fin 7 → M.Carrier .set) (G P F J f : M.Carrier .set) : Prop :=
  ∀ i child, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i child f → ForcingHS.HS actionFormula v G P F child

theorem familyHS_semantics {m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin m) (G P F J f : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (familyHS rho G P F J f) ↔
      FamilyHS (fun i => env (rho i)) (env G) (env P) (env F) (env J) (env f) := by
  simp only [familyHS,FamilyHS,Formula.Realize,KuratowskiZF.source_edge,ForcingHS.hs_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def moveEntries {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (J f P a : Fin m) : Formula m :=
  let up := paramsUp (paramsUp (paramsUp (paramsUp rho)))
  let jj := J.castSucc.castSucc.castSucc.castSucc
  let ff := f.castSucc.castSucc.castSucc.castSucc
  let pp := P.castSucc.castSucc.castSucc.castSucc
  let aa := a.castSucc.castSucc.castSucc.castSucc
  let x := (Fin.last m).castSucc.castSucc.castSucc
  let p := (Fin.last (m+1)).castSucc.castSucc
  let y := (Fin.last (m+2)).castSucc
  let q := Fin.last (m+3)
  .all (.all (.all (.all ((admissible R up jj ff pp x p).imp
    ((action pp aa x y).imp ((Source.SetLanguage.edge aa p q).imp (admissible R up jj ff pp y q)))))))

def MoveEntries {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (J f P a : M.Carrier .set) : Prop :=
  ∀ child p image q, Admissible R env J f P child p → Action P a child image →
    PureKuratowski.PairMember M p q a → Admissible R env J f P image q

theorem moveEntries_semantics {n m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (J f P a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (moveEntries R rho J f P a) ↔
      MoveEntries R (fun i => env (rho i)) (env J) (env f) (env P) (env a) := by
  simp only [moveEntries,MoveEntries,Formula.Realize,ForcingCollectedName.admissible_semantics (M := M),
    ForcingStabilizer.action_semantics (M := M),KuratowskiZF.source_edge,paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def permutes {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (H J f P : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) H.castSucc).imp (.all
    ((rel actionFormula (paramsUp (paramsUp ra)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (moveEntries R (paramsUp (paramsUp rho)) J.castSucc.castSucc f.castSucc.castSucc
        P.castSucc.castSucc (Fin.last (m+1))))))

def Permutes {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (H J f P : M.Carrier .set) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g H → ∀ a,
    MapRel actionFormula v g a → MoveEntries R env J f P a

theorem permutes_semantics {n m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (ra : Fin 7 → Fin m) (H J f P : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (permutes R rho ra H J f P) ↔
      Permutes R (fun i => env (rho i)) (fun i => env (ra i)) (env H) (env J) (env f) (env P) := by
  simp only [permutes,Permutes,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    moveEntries_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Literal source contract: a moved selected family entry has a selected index. -/
def IndexedPermutes {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (H J f P : M.Carrier .set) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g H → ∀ a,
    MapRel actionFormula v g a → ∀ i child p,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i child f →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p P → MapRel R env i p →
    ∃ j image q, (Definitional.Project.FirstOrderSemantics.reduct M).mem j J ∧
      PureKuratowski.PairMember M j image f ∧ MapRel R env j q ∧
      Action P a child image ∧ PureKuratowski.PairMember M p q a

theorem indexed_permutes_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (H J f : M.Carrier .set) :
    IndexedPermutes R env v H J f (v 6) ↔ Permutes R env v H J f (v 6) := by
  constructor
  · intro h g hg a hga child p image q had hm hpq
    have ha := (ForcingProductFamily.action_permutation ((mapRel_action v g a).mp hga)).1
    obtain ⟨i,hi,hic,hR⟩ := had.2
    obtain ⟨j,y,r,hj,hjy,hRj,hmy,hpr⟩ := h g hg a hga i child p hi hic had.1 hR
    have hy := ForcingNameConjugacy.unique hM ha hmy hm
    have hr := ForcingConditionGraphs.function_unique ha.1 hpr hpq
    subst y
    subst r
    exact ⟨ha.2 p q hpq,j,hj,hjy,hRj⟩
  · intro h g hg a hga i child p hi hic hp hR
    have ha := (ForcingProductFamily.action_permutation ((mapRel_action v g a).mp hga)).1
    obtain ⟨image,hm⟩ := ForcingNameConjugacy.exists_action hM ha child
    obtain ⟨q,hpq,_⟩ := ha.1.2 p hp
    obtain ⟨_,j,hj,hjy,hRj⟩ := h g hg a hga child p image q ⟨hp,i,hi,hic,hR⟩ hm hpq
    exact ⟨j,image,q,hj,hjy,hRj,hm,hpq⟩

theorem mapped_subset (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {J f P a name out : M.Carrier .set}
    (ha : ForcingConditionGraphs.Endomap P a) (hn : Collected R env J f P name)
    (hmove : MoveEntries R env J f P a) (hout : Action P a name out) :
    ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z out →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z name := by
  have hf := ForcingConditionAction.act_function (args2 P a) (0 : Fin 2) 1 ha
  intro z hz
  obtain ⟨child,p,image,q,he,hm,hq,hc⟩ := (ForcingMapConditions.mem_mapping hM hf hout z).mp hz
  have had := (ForcingCollectedName.edge_collected hM hn child p).mp he
  have hpq := (ForcingConditionAction.act_inside had.1).mp
    ((ForcingConditionAction.relation_semantics (args2 P a) (0 : Fin 2) 1 p q).mp hq)
  exact (hn z).mpr ⟨image,q,hmove child p image q had hm hpq,hc⟩

theorem fixed (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H J f name g a : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hH : ForcingConjugationGraph.Subgroup I G H)
    (hfamily : FamilyHS v G (v 6) F J f) (hperm : Permutes R env v H J f (v 6))
    (hn : Collected R env J f (v 6) name)
    (hg : (Definitional.Project.FirstOrderSemantics.reduct M).mem g H)
    (hga : MapRel actionFormula v g a) : Action (v 6) a name name := by
  have ha := (mapRel_action v g a).mp hga
  have har := ForcingProductFamily.action_permutation ha
  obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM har.1 name
  obtain ⟨inv,hi,hgi⟩ := hH.2.2.1 g hg
  obtain ⟨b,hb⟩ := ForcingProductFamily.exists_action hM hp ((hG inv).mp (hH.1 inv hi))
  have hbar := ForcingProductFamily.action_permutation hb
  have hab := ForcingProductCovariance.inverse hM hp ((hG g).mp (hH.1 g hg)) hgi ha hb
  have hbackMove := hperm inv hi b ((mapRel_action v inv b).mpr hb)
  have hfn := ForcingConditionAction.act_function (args2 (v 6) a) (0 : Fin 2) 1 har.1
  have heq : out = name := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · exact mapped_subset hM har.1 hn (hperm g hg a hga) hout z
    · intro hz
      obtain ⟨child,p,had,hc⟩ := (hn z).mp hz
      obtain ⟨old,ho,hop⟩ := har.2.2 p had.1
      obtain ⟨back,hback⟩ := ForcingNameConjugacy.exists_action hM hbar.1 child
      have hbEntry := hbackMove child p back old had hback ((hab old p).mp hop)
      obtain ⟨i,hiJ,hic,_⟩ := had.2
      have hforward := ForcingNameConjugacy.inverse_action hM hbar.1 har.1
        (fun x y => (hab y x).symm) (ForcingHS.isName (hfamily i child hiJ hic)) hback
      exact (ForcingMapConditions.mem_mapping hM hfn hout z).mpr
        ⟨back,old,child,p,(ForcingCollectedName.edge_collected hM hn back old).mpr hbEntry,hforward,
          (ForcingConditionAction.relation_semantics (args2 (v 6) a) (0 : Fin 2) 1 old p).mpr
            (Or.inl ⟨ho,hop⟩),hc⟩
  exact heq ▸ hout

theorem collect_HS (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H J f name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : ForcingConjugationGraph.Subgroup I G H)
    (hHF : (Definitional.Project.FirstOrderSemantics.reduct M).mem H F)
    (hfamily : FamilyHS v G (v 6) F J f) (hperm : Permutes R env v H J f (v 6))
    (hn : Collected R env J f (v 6) name) : ForcingHS.HS actionFormula v G (v 6) F name := by
  have hname := ForcingCollectedName.isName hM hn (fun i child hi hic => ForcingHS.isName (hfamily i child hi hic))
  apply ForcingHS.intro_hs hM actionFormula v G (v 6) F name hname
  · obtain ⟨S,hS⟩ := ForcingStabilizer.exists_stabilizer hM actionFormula v G (v 6) name
    refine ⟨S,hS,hF.2.1 H S hHF (ForcingProductStabilizer.subgroup hM v hp hG hname hS) ?_⟩
    intro g hg
    obtain ⟨a,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG g).mp (hH.1 g hg))
    have hga := (mapRel_action v g a).mpr ha
    exact (hS g).mpr ⟨hH.1 g hg,a,hga,fixed hM R env v hp hG hH hfamily hperm hn hg hga⟩
  · intro child p he
    obtain ⟨_,i,hi,hic,_⟩ := (ForcingCollectedName.edge_collected hM hn child p).mp he
    exact hfamily i child hi hic

def sentence {n : Nat} (R : Formula (n+2)) (rho : Fin 7 → Fin n) (I K B w G F H J f : Fin n) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
      ((ForcingConjugationGraph.subgroup I G H).imp ((Formula.mem H F).imp
        ((familyHS rho G (rho 6) F J f).imp ((permutes R id rho H J f (rho 6)).imp
          (.ex ((collected R (paramsUp id) J.castSucc f.castSucc (rho 6).castSucc (Fin.last n)).conj
            (ForcingHS.hs actionFormula (paramsUp rho) G.castSucc (rho 6).castSucc F.castSucc (Fin.last n))))))))))).close

theorem models {n : Nat} (R : Formula (n+2)) (rho : Fin 7 → Fin n) (I K B w G F H J f : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (sentence R rho I K B w G F H J f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF hH hHF hf hperm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w
    (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF
  have hH' := (ForcingConjugationGraph.subgroup_semantics (M := M) env I G H).mp hH
  have hf' := (familyHS_semantics (M := M) env rho G (rho 6) F J f).mp hf
  have hperm' := (permutes_semantics (M := M) env R id rho H J f (rho 6)).mp hperm
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM R env (env J) (env f) (env (rho 6))
  have hHS := collect_HS hM R env (fun j => env (rho j)) hp' hG' hF' hH' hHF hf' hperm' hn
  refine ⟨name,?_,?_⟩
  · apply (ForcingCollectedName.collected_semantics (M := M) (Fin.lastCases name env) R (paramsUp id)
      J.castSucc f.castSucc (rho 6).castSucc (Fin.last n)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hn
  · apply (ForcingHS.hs_semantics (M := M) (Fin.lastCases name env) actionFormula (paramsUp rho)
      G.castSucc (rho 6).castSucc F.castSucc (Fin.last n)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using hHS

theorem kernel_certificate {n : Nat} (R : Formula (n+2)) (rho : Fin 7 → Fin n) (I K B w G F H J f : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R rho I K B w G F H J f)) :=
  ModelTransfer.derives (fun _ hM => models R rho I K B w G F H J f hM)

end PPAC.Migration.ForcingCollectedHS
