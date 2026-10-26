/- SymmetricChoice.replacementBound: the set-group orbit of a set of local
HS witnesses. The source chosen family will be supplied by native Collection.
Reuse native functional images and the existing actual name action. -/
import PPAC.Migration.ForcingPowerName

namespace PPAC.Migration.ForcingReplacementOrbit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingStabilizer (Action)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingHS (HS)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The precise source action, at an internal group element. -/
def Moved (v : Fin 7 → M.Carrier .set) (g eta out : M.Carrier .set) : Prop :=
  ∃ a, MapRel actionFormula v g a ∧ Action (v 6) a eta out

def moved {m : Nat} (rho : Fin 7 → Fin m) (g eta out : Fin m) : Formula m :=
  .ex ((ReplacementPredicates.rel actionFormula (paramsUp rho) g.castSucc (Fin.last m)).conj
    (ForcingStabilizer.action (rho 6).castSucc (Fin.last m) eta.castSucc out.castSucc))

theorem moved_semantics {m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin m) (g eta out : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (moved rho g eta out) ↔
      Moved (fun j => env (rho j)) (env g) (env eta) (env out) := by
  simp only [moved,Moved,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingStabilizer.action_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Orbit (v : Fin 7 → M.Carrier .set) (G W out : M.Carrier .set) : Prop :=
  ∃ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G ∧ ∃ eta,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W ∧ Moved v g eta out

def MovePair (v : Fin 7 → M.Carrier .set) (G W z out : M.Carrier .set) : Prop :=
  ∃ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G ∧ ∃ eta,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W ∧ PureKuratowski.Code M z g eta ∧ Moved v g eta out

def movePair {m : Nat} (rho : Fin 7 → Fin m) (G W z out : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) G.castSucc).conj (.ex
    ((Formula.mem (Fin.last (m+1)) W.castSucc.castSucc).conj
      ((PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
        (moved (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1)) out.castSucc.castSucc)))))

theorem movePair_semantics {m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin m) (G W z out : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (movePair rho G W z out) ↔
      MovePair (fun j => env (rho j)) (env G) (env W) (env z) (env out) := by
  simp only [movePair,MovePair,Formula.Realize,moved_semantics (M := M),KuratowskiZF.source_code,
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem moved_unique (hM : FirstOrder.Theory.Models M nativeZF) {v : Fin 7 → M.Carrier .set}
    {g eta out out' : M.Carrier .set} (h : Moved v g eta out) (h' : Moved v g eta out') : out = out' := by
  obtain ⟨a,ha,hm⟩ := h
  obtain ⟨b,hb,hm'⟩ := h'
  have heq := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp ha) ((mapRel_action _ _ _).mp hb)
  subst b
  exact ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp ha)).1 hm hm'

theorem exists_orbit (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (W : M.Carrier .set) :
    ∃ O, ∀ out, (Definitional.Project.FirstOrderSemantics.reduct M).mem out O ↔ Orbit v G W out := by
  obtain ⟨J,hJ⟩ := ForcingCohenCoordinates.exists_cartesian hM G W
  let inputs : Fin 9 → M.Carrier .set := Fin.lastCases W (Fin.lastCases G v)
  let ra : Fin 7 → Fin 11 := fun j => j.castSucc.castSucc.castSucc.castSucc
  let gg : Fin 11 := (Fin.last 7).castSucc.castSucc.castSucc
  let ww : Fin 11 := (Fin.last 8).castSucc.castSucc
  let zz : Fin 11 := (Fin.last 9).castSucc
  let oo : Fin 11 := Fin.last 10
  let matrix := movePair ra gg ww zz oo
  have hm : ∀ z out, MapRel matrix inputs z out ↔ MovePair v G W z out := by
    intro z out
    simpa only [MapRel,inputs,ra,gg,ww,zz,oo,Fin.lastCases_last,Fin.lastCases_castSucc] using
      movePair_semantics (M := M) (Fin.lastCases out (Fin.lastCases z inputs)) ra gg ww zz oo
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 9 :=
    { bound := fun j => inputs j.rev, free := fun _ => J }
  have hr := ForcingMapConditions.binary_semantics hM matrix inputs J
  obtain ⟨O,hO⟩ := SetTheory.ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary matrix) env J (by
      intro z hz
      obtain ⟨g,hg,eta,heta,hcode⟩ := (hJ z).mp hz
      obtain ⟨a,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG g).mp hg)
      obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation ha).1 eta
      exact ⟨out,(hr z out).mpr ((hm z out).mpr ⟨g,hg,eta,heta,hcode,a,(mapRel_action _ _ _).mpr ha,hout⟩)⟩) (by
      intro z out out' ho ho'
      obtain ⟨g,_,eta,_,hc,ha⟩ := (hm z out).mp ((hr z out).mp ho)
      obtain ⟨g',_,eta',_,hc',ha'⟩ := (hm z out').mp ((hr z out').mp ho')
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc'
      exact moved_unique hM ha ha')
  refine ⟨O,fun out => ?_⟩
  constructor
  · intro ho
    obtain ⟨z,_,hz⟩ := (hO out).mp ho
    obtain ⟨g,hg,eta,heta,_,hmove⟩ := (hm z out).mp ((hr z out).mp hz)
    exact ⟨g,hg,eta,heta,hmove⟩
  · rintro ⟨g,hg,eta,heta,hmove⟩
    obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM g eta
    exact (hO out).mpr ⟨z,(hJ z).mpr ⟨g,hg,eta,heta,hz⟩,
      (hr z out).mpr ((hm z out).mpr ⟨g,hg,eta,heta,hz,hmove⟩)⟩

/-- The source multiplication-of-orbits calculation, using actual graph laws. -/
theorem orbit_move (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G W h a child image : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G)
    (hh : (Definitional.Project.FirstOrderSemantics.reduct M).mem h G)
    (ha : MapRel actionFormula v h a) (hc : Orbit v G W child) (hi : Action (v 6) a child image) :
    Orbit v G W image := by
  obtain ⟨g,hg,eta,heta,b,hb,hm⟩ := hc
  obtain ⟨product,hprod,hcomp⟩ := ForcingConditionGraphs.exists_composition hM ((hG h).mp hh) ((hG g).mp hg)
  obtain ⟨c,hc⟩ := ForcingProductFamily.exists_action hM hp hprod
  have hab := ForcingProductFamily.multiplication hM hp ((hG g).mp hg) hcomp
    ((mapRel_action _ _ _).mp ha) ((mapRel_action _ _ _).mp hb) hc
  exact ⟨product,(hG product).mpr hprod,eta,heta,c,(mapRel_action _ _ _).mpr hc,
    ForcingNameConjugacy.composition hM (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp ha)).1
      (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hb)).1 hab hm hi⟩

theorem orbit_contains (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G W eta : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hn : ForcingNames.IsName (v 6) eta)
    (he : (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W) : Orbit v G W eta := by
  obtain ⟨g,hg,hgi⟩ := ForcingConditionGraphs.exists_identity hM I
  obtain ⟨a,ha⟩ := ForcingProductFamily.exists_action hM hp hg
  have hai := ForcingProductFamily.identity hM hp hgi ha
  exact ⟨g,(hG g).mpr hg,eta,he,a,(mapRel_action _ _ _).mpr ha,
    ForcingConditionAction.name_identity hM (args2 (v 6) a) (0 : Fin 2) 1 hai eta hn⟩

/-- Source replacementBound construction from a collected set of HS seeds.
The entire group fixes this bound; every seed belongs at every condition. -/
theorem exists_bound (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F W : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hW : ∀ eta, (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W → HS actionFormula v G (v 6) F eta) :
    ∃ bound, HS actionFormula v G (v 6) F bound ∧
      (∀ child p, PureKuratowski.PairMember M child p bound ↔
        (Definitional.Project.FirstOrderSemantics.reduct M).mem p (v 6) ∧ Orbit v G W child) ∧
      ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G → ∀ a,
        MapRel actionFormula v g a → Action (v 6) a bound bound := by
  obtain ⟨O,hO⟩ := exists_orbit hM v hp hG W
  obtain ⟨f,_,hf⟩ := ForcingConditionGraphs.exists_identity hM O
  have hfamily : ForcingCollectedHS.FamilyHS v G (v 6) F O f := by
    intro i child _ hic
    obtain ⟨hi,rfl⟩ := (hf i child).mp hic
    obtain ⟨g,hg,eta,heta,a,ha,hm⟩ := (hO i).mp hi
    exact ForcingPowerName.hs_move hM v hp hG hF ((hG g).mp hg) ha (hW eta heta) hm
  have hperm : ForcingCollectedHS.Permutes ForcingPowerName.trueTest Fin.elim0 v G O f (v 6) := by
    intro g hg a hga child p image q had him hpq
    obtain ⟨_,i,hi,hic,_⟩ := had
    obtain ⟨_,rfl⟩ := (hf i child).mp hic
    have himage := (hO image).mpr (orbit_move hM v hp hG hg hga ((hO i).mp hi) him)
    exact ⟨(ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hga)).1.2 p q hpq,
      image,himage,(hf image image).mpr ⟨himage,rfl⟩,fun h => h⟩
  obtain ⟨bound,hb⟩ := ForcingCollectedName.exists_collected hM ForcingPowerName.trueTest Fin.elim0 O f (v 6)
  have htop := ForcingSupportFilter.top_subgroup hM hG
  refine ⟨bound,ForcingCollectedHS.collect_HS hM ForcingPowerName.trueTest Fin.elim0 v hp hG hF htop hF.1 hfamily hperm hb,?_,
    fun g hg a ha => ForcingCollectedHS.fixed hM ForcingPowerName.trueTest Fin.elim0 v hp hG htop hfamily hperm hb hg ha⟩
  intro child p
  rw [ForcingCollectedName.edge_collected hM hb child p]
  constructor
  · rintro ⟨hp,i,hi,hic,_⟩
    obtain ⟨_,rfl⟩ := (hf i child).mp hic
    exact ⟨hp,(hO i).mp hi⟩
  · rintro ⟨hp,hchild⟩
    have hi := (hO child).mpr hchild
    exact ⟨hp,child,hi,(hf child child).mpr ⟨hi,rfl⟩,fun h => h⟩

end PPAC.Migration.ForcingReplacementOrbit
