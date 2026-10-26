/- Pinned SymmetricSets.SubsetF/subsetBound/normalize/PowerCandidate/power.
Normalization bounds codes of subsets of one name, never the HS universe. -/
import PPAC.Migration.ForcingSeparationAxiom
import PPAC.Migration.ForcingBasicSetAxioms

namespace PPAC.Migration.ForcingPowerName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingStabilizer (Action)
open ForcingHS (HS)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Subset (x y : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z x →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z y

def SubsetF {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P p sigma tau : M.Carrier .set) : Prop :=
  ∀ nu, Predicate H env nu → ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P →
    MapRel R env q p → Forces false R env P nu sigma q → Forces false R env P nu tau q

def subsetF {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (P p sigma tau : Fin m) : Formula m :=
  .all ((MinimalPredicates.pred H (paramsUp rho) (Fin.last m)).imp (.all
    ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
      ((ReplacementPredicates.rel R (paramsUp (paramsUp rho)) (Fin.last (m+1)) p.castSucc.castSucc).imp
        ((ForcingAtomicRelations.forces false R (paramsUp (paramsUp rho)) P.castSucc.castSucc
          (Fin.last m).castSucc sigma.castSucc.castSucc (Fin.last (m+1))).imp
          (ForcingAtomicRelations.forces false R (paramsUp (paramsUp rho)) P.castSucc.castSucc
            (Fin.last m).castSucc tau.castSucc.castSucc (Fin.last (m+1))))))))

theorem subsetF_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m) (P p sigma tau : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (subsetF R H rho P p sigma tau) ↔
      SubsetF R H (fun j => env (rho j)) (env P) (env p) (env sigma) (env tau) := by
  simp only [subsetF,SubsetF,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem forces_subset (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a b : Fin n) :
    Force R H env v P p (Source.SetLanguage.subset a b) ↔ SubsetF R H env P p (v a) (v b) := by
  unfold Source.SetLanguage.subset
  rw [ForcingSound.rename hM hpre _ _ _ _ hp, ForcingFormula.force_all hM hpre hp]
  simp only [ForcingFormula.force_imp hM hpre hp,ForcingFormula.force_mem,SubsetF]
  rfl

theorem subset_mono {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {P p q sigma tau : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Definitional.Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (h : SubsetF R H env P p sigma tau) : SubsetF R H env P q sigma tau :=
  fun nu hnu r hr hrq => h nu hnu r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem subset_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p sigma tau : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ SubsetF R H env P r sigma tau) :
    SubsetF R H env P p sigma tau := by
  intro nu hnu q hq hqp hmem
  apply ForcingAtomicBasic.mem_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,hsub⟩ := h r hr (hpre.2 r q p hr hq hp hrq hqp)
  exact ⟨s,hs,hsr,hsub nu hnu s hs (hpre.1 s hs)
    (ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hmem)⟩

theorem subset_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p sigma sigma' tau tau' : M.Carrier .set}
    (hpre : PreorderOn R env P) (hs : Forces true R env P sigma sigma' p) (ht : Forces true R env P tau tau' p) :
    SubsetF R H env P p sigma tau ↔ SubsetF R H env P p sigma' tau' := by
  constructor
  · intro h nu hnu q hq hqp hm
    exact (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp ht)).mp
      (h nu hnu q hq hqp ((ForcingAtomicLaws.mem_congr_right hM hpre
        (ForcingAtomicBasic.eq_mono hM hpre hq hqp hs)).mpr hm))
  · intro h nu hnu q hq hqp hm
    exact (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp ht)).mpr
      (h nu hnu q hq hqp ((ForcingAtomicLaws.mem_congr_right hM hpre
        (ForcingAtomicBasic.eq_mono hM hpre hq hqp hs)).mp hm))

def Bound (P sigma bound : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z bound ↔
    ∃ child c, PureKuratowski.PairMember M child c sigma ∧ ∃ p,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ PureKuratowski.Code M z child p

def trueTest : Formula 2 := .imp .bot .bot

theorem bound_collected {P sigma f bound : M.Carrier .set}
    (hf : ForcingSeparation.Family sigma f)
    (hb : ForcingCollectedName.Collected trueTest Fin.elim0 sigma f P bound) : Bound P sigma bound := by
  intro z
  rw [hb z]
  constructor
  · rintro ⟨child,p,⟨hp,i,hi,hic,_⟩,hcode⟩
    obtain ⟨_,c,hic'⟩ := (hf i child).mp hic
    exact ⟨child,c,⟨i,hic',hi⟩,p,hp,hcode⟩
  · rintro ⟨child,c,⟨i,hic,hi⟩,p,hp,hcode⟩
    exact ⟨child,p,⟨hp,i,hi,(hf i child).mpr ⟨hi,c,hic⟩,fun h => h⟩,hcode⟩

/-- Source mapConditions_mono, directly from its exact entry equation. -/
theorem map_subset (hM : FirstOrder.Theory.Models M nativeZF) {P a sigma tau out out' : M.Carrier .set}
    (ha : ForcingConditionGraphs.Endomap P a) (hs : Subset sigma tau)
    (hmap : Action P a sigma out) (hmap' : Action P a tau out') : Subset out out' := by
  intro z hz
  have hf := ForcingConditionAction.act_function (args2 P a) (0 : Fin 2) 1 ha
  obtain ⟨child,p,image,q,⟨code,hcode,hc⟩,hm,hq,hzcode⟩ := (ForcingMapConditions.mem_mapping hM hf hmap z).mp hz
  exact (ForcingMapConditions.mem_mapping hM hf hmap' z).mpr
    ⟨child,p,image,q,⟨code,hcode,hs code hc⟩,hm,hq,hzcode⟩

/-- Keep the particular source stabilizer, needed by powerCandidate_permute. -/
theorem exists_bound (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F sigma : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hs : HS actionFormula v G (v 6) F sigma) :
    ∃ S bound, ForcingStabilizer.Stabilizer actionFormula v G (v 6) sigma S ∧
      ForcingConjugationGraph.Subgroup I G S ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem S F ∧
      Bound (v 6) sigma bound ∧ ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g S →
        ∀ a, MapRel actionFormula v g a → Action (v 6) a bound bound := by
  obtain ⟨S,hS,hSF⟩ := ForcingHS.symmetric_of_hs hs
  have hSG := ForcingProductStabilizer.subgroup hM v hp hG (ForcingHS.isName hs) hS
  obtain ⟨f,hf⟩ := ForcingSeparation.exists_family hM sigma
  obtain ⟨bound,hb⟩ := ForcingCollectedName.exists_collected hM trueTest Fin.elim0 sigma f (v 6)
  have hfamily : ForcingCollectedHS.FamilyHS v G (v 6) F sigma f := by
    intro i child _ hic
    obtain ⟨hi,c,hcode⟩ := (hf i child).mp hic
    exact ForcingHS.child hs ⟨i,hcode,hi⟩
  have hperm : ForcingCollectedHS.Permutes trueTest Fin.elim0 v S sigma f (v 6) := by
    intro g hg a hga child p image q had him hpq
    have ha := (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hga)).1
    obtain ⟨_,b,hgb,hfix⟩ := (hS g).mp hg
    have hba := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp hgb) ((mapRel_action _ _ _).mp hga)
    subst b
    obtain ⟨hcond,i,hi,hic,_⟩ := had
    obtain ⟨_,c,hcode⟩ := (hf i child).mp hic
    obtain ⟨image',c',he,him',_⟩ := ForcingSeparation.entry_permute hM ha (ForcingHS.isName hs) hfix ⟨i,hcode,hi⟩
    have heq := ForcingNameConjugacy.unique hM ha him' him
    subst image'
    obtain ⟨j,hjc,hj⟩ := he
    exact ⟨ha.2 p q hpq,j,hj,(hf j image).mpr ⟨hj,c',hjc⟩,fun h => h⟩
  exact ⟨S,bound,hS,hSG,hSF,bound_collected hf hb,
    fun g hg a hga => ForcingCollectedHS.fixed hM trueTest Fin.elim0 v hp hG hSG hfamily hperm hb hg hga⟩

def Candidates (v : Fin 7 → M.Carrier .set) (G F bound C : M.Carrier .set) : Prop :=
  ∀ nu, (Definitional.Project.FirstOrderSemantics.reduct M).mem nu C ↔
    HS actionFormula v G (v 6) F nu ∧ Subset nu bound

def candidate {m : Nat} (rho : Fin 7 → Fin m) (G F bound nu : Fin m) : Formula m :=
  (ForcingHS.hs actionFormula rho G (rho 6) F nu).conj (Source.SetLanguage.subset nu bound)

theorem candidate_semantics {m : Nat} (env : Fin m → M.Carrier .set)
    (rho : Fin 7 → Fin m) (G F bound nu : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (candidate rho G F bound nu) ↔
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env nu) ∧ Subset (env nu) (env bound) := by
  simp only [candidate,Formula.Realize,ForcingHS.hs_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M)]
  rfl

/-- Reuse the native powerset and Separation to construct every HS candidate. -/
theorem exists_candidates (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    (G F bound : M.Carrier .set) : ∃ C, Candidates v G F bound C := by
  obtain ⟨power,hpower⟩ := SetTheory.ZF.exists_powerSet (ModelTransfer.project_models_iff.mp hM) bound
  let env : Fin 10 → M.Carrier .set := Fin.lastCases bound (Fin.lastCases F (Fin.lastCases G v))
  let rho : Fin 7 → Fin 10 := fun j => j.castSucc.castSucc.castSucc
  let gg : Fin 10 := (Fin.last 7).castSucc.castSucc
  let ff : Fin 10 := (Fin.last 8).castSucc
  let bb : Fin 10 := Fin.last 9
  let query := candidate (paramsUp rho) gg.castSucc ff.castSucc bb.castSucc (Fin.last 10)
  have hq : ∀ nu, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases nu env) query ↔
      HS actionFormula v G (v 6) F nu ∧ Subset nu bound := by
    intro nu
    simpa only [query,env,rho,gg,ff,bb,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using
      candidate_semantics (M := M) (Fin.lastCases nu env) (paramsUp rho) gg.castSucc ff.castSucc bb.castSucc (Fin.last 10)
  have hsep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨C,hC⟩ := hsep env power
  refine ⟨C,fun nu => ?_⟩
  exact ⟨fun h => (hq nu).mp ((hC nu).mp h).2,
    fun h => (hC nu).mpr ⟨(hpower nu).mpr h.2,(hq nu).mpr h⟩⟩

theorem hs_move (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F g a sigma out : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hg : ForcingConditionGraphs.Permutation I g) (ha : MapRel actionFormula v g a)
    (hs : HS actionFormula v G (v 6) F sigma) (hm : Action (v 6) a sigma out) : HS actionFormula v G (v 6) F out := by
  obtain ⟨inv,hinv,hgi⟩ := ForcingConditionGraphs.exists_inverse hM hg
  obtain ⟨b,hb⟩ := ForcingProductFamily.exists_action hM hp hinv
  obtain ⟨c,hcc,hc⟩ := ForcingConjugationGraph.exists_graph hM hG hg hinv hgi
  exact ForcingHSAction.hs_action hM
    (ForcingSeparation.normal_context hM v hp hG hF hg hinv hgi hcc hc ha ((mapRel_action _ _ _).mpr hb)) sigma hs out hm

theorem subset_symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w g a sigma tau sigma' tau' p q : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hg : ForcingConditionGraphs.Permutation I g) (ha : MapRel actionFormula (fun j => env (rho j)) g a)
    (hs : Action (env (rho 6)) a sigma sigma') (ht : Action (env (rho 6)) a tau tau')
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q a) :
    SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p sigma tau ↔
      SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) q sigma' tau' := by
  have hq := (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp ha)).1.2 p q hpq
  have hv : ∀ j, Action (env (rho 6)) a (args2 sigma tau j) (args2 sigma' tau' j) := by
    intro j
    refine Fin.cases hs (fun i => ?_) j
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ht
  exact (forces_subset hM hpre hcond (args2 sigma tau) 0 1).symm.trans
    ((ForcingSeparation.symmetry hM env rho G F mul hp hG hF hg ha
      (Source.SetLanguage.subset (0 : Fin 2) 1) (args2 sigma tau) (args2 sigma' tau') hv hcond hpq).trans
      (forces_subset hM hpre hq (args2 sigma' tau') 0 1))

def subsetTest {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P sigma : Fin k) : Formula (k+2) :=
  subsetF R H (fun j => j.castSucc.castSucc) P.castSucc.castSucc (Fin.last (k+1)) (Fin.last k).castSucc sigma.castSucc.castSucc

theorem subsetTest_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (P sigma : Fin k) (nu p : M.Carrier .set) :
    MapRel (subsetTest R H P sigma) env nu p ↔ SubsetF R H env (env P) p nu (env sigma) := by
  unfold MapRel subsetTest
  rw [subsetF_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Every separated normalization lies in the one source bound. -/
theorem normalized_bounded {k n : Nat}
    {A : Formula (k+2)} {aenv : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {H : Formula (n+1)} {env : Fin n → M.Carrier .set}
    {G P F sigma nu name bound : M.Carrier .set}
    (hb : Bound P sigma bound) (hn : HS A aenv G P F name)
    (hs : ForcingSeparation.Separated R H env (fun _ : Fin 1 => nu) P sigma name (.mem (1 : Fin 2) 0)) : Subset name bound := by
  intro z hz
  obtain ⟨child,p,hcode,hp,_⟩ := ForcingNames.edges (ForcingHS.isName hn) z hz
  obtain ⟨⟨c,he⟩,_,_,_⟩ := (hs child p).mp ⟨z,hcode,hz⟩
  exact (hb z).mpr ⟨child,c,he,p,hp,hcode⟩

/-- Literal source normalize = separate sigma [nu] (mem 1 0). -/
theorem exists_normalize (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w sigma nu bound : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (hnu : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu)
    (hb : Bound (env (rho 6)) sigma bound) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧ Subset name bound ∧
      ∀ child p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child name p ↔
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child sigma p ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child nu p) := by
  obtain ⟨name,hn,hsep⟩ := ForcingSeparationAxiom.exists_at_values hM env rho G F mul hp hG hF hs
    (fun _ : Fin 1 => nu) (fun _ => hnu) (.mem (1 : Fin 2) 0)
  refine ⟨name,hn,normalized_bounded hb hn hsep,?_⟩
  intro child p hcond
  simpa only [ForcingFormula.force_mem,show (1 : Fin 2) = Fin.last 1 from rfl,
    show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc] using
    ForcingSeparationAxiom.mem_separate hM hpre hsep hcond (nu := child)


/-- Literal powerCandidate_permute and collect, using all internal HS subsets
of the source normalization bound. No choice of a family of witnesses. -/
theorem exists_power (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul sigma : Fin k)
    {I K B w : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env sigma)) :
    ∃ bound name, Bound (env (rho 6)) (env sigma) bound ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      ∀ child p, PureKuratowski.PairMember M child p name ↔
        HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) child ∧
        Subset child bound ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) ∧
        SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p child (env sigma) := by
  let v := fun j => env (rho j)
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let T := subsetTest R H (rho 6) sigma
  obtain ⟨S,bound,hS,hSG,hSF,hbound,hfixed⟩ := exists_bound hM v hp hG hs
  obtain ⟨C,hC⟩ := exists_candidates hM v (env G) (env F) bound
  obtain ⟨f,_,hf⟩ := ForcingConditionGraphs.exists_identity hM C
  have hfamily : ForcingCollectedHS.FamilyHS v (env G) (env (rho 6)) (env F) C f := by
    intro i child _ hic
    obtain ⟨hi,heq⟩ := (hf i child).mp hic
    exact heq ▸ ((hC i).mp hi).1
  have hperm : ForcingCollectedHS.Permutes T env v S C f (env (rho 6)) := by
    intro g hg a hga child p image q had him hpq
    obtain ⟨hcond,i,hi,hic,htest⟩ := had
    obtain ⟨_,heq⟩ := (hf i child).mp hic
    subst i
    obtain ⟨hchild,hsub⟩ := (hC child).mp hi
    have ha := (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hga)).1
    have hgG := (hG g).mp (hSG.1 g hg)
    have himage := hs_move hM v hp hG hF hgG hga hchild him
    have hb := map_subset hM ha hsub him (hfixed g hg a hga)
    have hiC := (hC image).mpr ⟨himage,hb⟩
    obtain ⟨_,b,hgb,hfix⟩ := (hS g).mp hg
    have hba := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp hgb) ((mapRel_action _ _ _).mp hga)
    subst b
    have htest' := (subset_symmetry hM env rho G F mul hp hG hF hpre hgG hga him hfix hcond hpq).mp
      ((subsetTest_semantics env R H (rho 6) sigma child p).mp htest)
    exact ⟨ha.2 p q hpq,image,hiC,(hf image image).mpr ⟨hiC,rfl⟩,
      (subsetTest_semantics env R H (rho 6) sigma image q).mpr htest'⟩
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM T env C f (env (rho 6))
  have hHS := ForcingCollectedHS.collect_HS hM T env v hp hG hF hSG hSF hfamily hperm hn
  refine ⟨bound,name,hbound,hHS,?_⟩
  intro child p
  rw [ForcingCollectedName.edge_collected hM hn child p]
  constructor
  · rintro ⟨hcond,i,hi,hic,ht⟩
    obtain ⟨_,heq⟩ := (hf i child).mp hic
    subst i
    exact ⟨((hC child).mp hi).1,((hC child).mp hi).2,hcond,
      (subsetTest_semantics env R H (rho 6) sigma child p).mp ht⟩
  · rintro ⟨hchild,hsub,hcond,ht⟩
    have hi := (hC child).mpr ⟨hchild,hsub⟩
    exact ⟨hcond,child,hi,(hf child child).mpr ⟨hi,rfl⟩,
      (subsetTest_semantics env R H (rho 6) sigma child p).mpr ht⟩


/-- Transport only parameter slots; the internal relation and HS domain stay equal. -/
theorem subset_relation_congr {k l : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {S : Formula (l+2)} {J : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {ext : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S ext x y)
    (hH : ∀ x, Predicate H env x ↔ Predicate J ext x)
    (P p sigma tau : M.Carrier .set) :
    SubsetF R H env P p sigma tau ↔ SubsetF S J ext P p sigma tau := by
  simp only [SubsetF,← hH,← hR,← ForcingSeparation.atomic_congr hR false]

/-- The source normalization equality, with no rank condition on nu. -/
theorem normalize_eq (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {sigma nu name p : M.Carrier .set}
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hn : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu)
    (hm : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hmem : ∀ child q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child name q ↔
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child sigma q ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child nu q))
    (hsub : SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p nu sigma) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) nu name p := by
  apply ForcingBasicSetAxioms.eq_of_same_members hM hpre hn hm hp
  intro child hc q hq hqp
  rw [hmem child q hq]
  exact ⟨fun h => ⟨hsub child ((domain_semantics env rho G F child).mpr hc) q hq hqp h,h⟩,And.right⟩

/-- Exact source mem_power: quantification includes every internal HS name. -/
theorem mem_power (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w sigma bound name nu p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (hnu : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu)
    (hb : Bound (env (rho 6)) sigma bound)
    (he : ∀ child q, PureKuratowski.PairMember M child q name ↔
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) child ∧
      Subset child bound ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) ∧
      SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) q child sigma)
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu name p ↔
      SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p nu sigma := by
  constructor
  · intro h
    apply subset_dense hM hpre hcond
    intro q hq hqp
    obtain ⟨r,child,c,hr,hrq,hc,hed,hrc,heq⟩ :=
      ((ForcingAtomicRelations.mem_iff hM _ env _ nu name p).mp h).2 q hq hqp
    have hsub := subset_mono hpre hc hr hrc ((he child c).mp hed).2.2.2
    exact ⟨r,hr,hrq,(subset_congr hM hpre heq (ForcingAtomicBasic.eq_refl hM hpre sigma r hr)).mpr hsub⟩
  · intro h
    obtain ⟨normal,hn,hnb,hnmem⟩ := exists_normalize hM env rho G F mul hp hG hF hpre hs hnu hb
    have heq := normalize_eq hM env rho G F mul hpre hnu hn hcond hnmem h
    have hsub := (subset_congr hM hpre heq (ForcingAtomicBasic.eq_refl hM hpre sigma p hcond)).mp h
    have hed := (he normal p).mpr ⟨hn,hnb,hcond,hsub⟩
    exact (ForcingAtomicLaws.mem_congr_left hM hpre heq).mpr
      (ForcingAtomicBasic.mem_of_edge_eq hM hpre hcond (hpre.1 p hcond) hed
        (ForcingAtomicBasic.eq_refl hM hpre normal p hcond))

end PPAC.Migration.ForcingPowerName


