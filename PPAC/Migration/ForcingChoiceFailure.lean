/- Fixed ChoiceFailure: literal outside-label names and the full choice-function
counterexample. Reuse the completed power/separation, support and placement
constructors; no external family of selected elements. -/
import PPAC.Migration.ForcingNonwellorderableImage
import PPAC.Migration.ForcingPowerAxiom
import PPAC.Migration.ForcingSeparationAxiom
import PPAC.Migration.ForcingLabelSeparation

namespace PPAC.Migration.ForcingChoiceFailure
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingClassEvaluation (Predicate)
open ForcingHS (HS)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

section Logic
variable (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
variable {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
variable {P p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
variable (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
include hM hpre hp

/-- Original ProductNames.forces_nonempty, over the full internal HS domain. -/
theorem forces_nonempty (v : Fin n → M.Carrier .set) (a : Fin n) :
    Force R H env v P p (Source.SetLanguage.nonempty a) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          ∃ x, Predicate H env x ∧ Forces false R env P x (v a) r := by
  rw [Source.SetLanguage.nonempty,ForcingSound.rename hM hpre _ _ _ _ hp]
  rfl

/-- Original ProductNames.functionOn_total; keep every graph-domain conjunct. -/
theorem functionOn_total (v : Fin n → M.Carrier .set) (f d : Fin n)
    (hf : Force R H env v P p (Source.SetLanguage.functionOn f d))
    {x q r : M.Carrier .set} (hx : Predicate H env x)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hxd : Forces false R env P x (v d) q)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r P) (hrq : MapRel R env r q) :
    ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ y, Predicate H env y ∧ Force R H env (args3 (v f) x y) P s (Source.SetLanguage.edge 0 1 2) ∧
        ∀ z, Predicate H env z → ∀ t, (Project.FirstOrderSemantics.reduct M).mem t P → MapRel R env t s →
          Force R H env (args3 (v f) x z) P t (Source.SetLanguage.edge 0 1 2) → Forces true R env P z y t := by
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hf.2 x hx
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxd
  obtain ⟨s,hs,hsr,y,hy,hxy,huniq⟩ := hh r hr hrq
  refine ⟨s,hs,hsr,y,hy,(ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 4) 2 3).mp hxy,?_⟩
  intro z hz t ht hts hxz
  have hu := (ForcingFormula.force_all hM hpre hs _ _).mp huniq z hz
  have hu := (ForcingFormula.force_imp hM hpre hs _ _ _).mp hu t ht hts
  exact hu ((ForcingRelationClass.edge_formula hM hpre ht _ (0 : Fin 5) 2 4).mpr hxz)

/-- Source graph uniqueness for unrestricted internal argument/value names. -/
theorem functionOn_unique (v : Fin n → M.Carrier .set) (f d : Fin n)
    (hf : Force R H env v P p (Source.SetLanguage.functionOn f d))
    {x y z : M.Carrier .set} (hx : Predicate H env x) (hy : Predicate H env y) (hz : Predicate H env z)
    (hxd : Forces false R env P x (v d) p)
    (hxy : Force R H env (args3 (v f) x y) P p (Source.SetLanguage.edge 0 1 2))
    (hxz : Force R H env (args3 (v f) x z) P p (Source.SetLanguage.edge 0 1 2)) :
    Forces true R env P y z p := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,a,_,_,hu⟩ := functionOn_total hM hpre hp v f d hf hx hp (hpre.1 p hp) hxd hq hqp
  have hrp := hpre.2 r q p hr hq hp hrq hqp
  exact ⟨r,hr,hrq,ForcingAtomicLaws.eq_trans hM hpre
    (hu y hy r hr (hpre.1 r hr) (ForcingFormula.mono hM hpre _ _ hp hr hrp hxy))
    (ForcingAtomicBasic.eq_symm hM (hu z hz r hr (hpre.1 r hr) (ForcingFormula.mono hM hpre _ _ hp hr hrp hxz)))⟩

/-- Original ProductNames.forces_choiceOn: the complete function formula and
actual membership of its chosen value, with no codomain shortcut. -/
theorem forces_choiceOn (v : Fin n → M.Carrier .set) (c A : Fin n) :
    Force R H env v P p (Source.SetLanguage.choiceOn c A) ↔
      Force R H env v P p (Source.SetLanguage.functionOn c A) ∧
      ∀ x, Predicate H env x → ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        Forces false R env P x (v A) q → ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
          ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
            ∃ y, Predicate H env y ∧ Force R H env (args3 (v c) x y) P s (Source.SetLanguage.edge 0 1 2) ∧
              Forces false R env P y x s := by
  rw [Source.SetLanguage.choiceOn,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  have hfunc : Force R H env (fun i => v (args2 c A i)) P p (Source.SetLanguage.functionOn 0 1) ↔
      Force R H env v P p (Source.SetLanguage.functionOn c A) := by
    rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,
      Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp]
    rfl
  rw [hfunc]
  constructor
  · rintro ⟨hf,hh⟩
    refine ⟨hf,?_⟩
    intro x hx q hq hqp hxd r hr hrq
    have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh x hx
    have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxd
    obtain ⟨s,hs,hsr,y,hy,hxy,hym⟩ := hh r hr hrq
    exact ⟨s,hs,hsr,y,hy,(ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 4) 2 3).mp hxy,hym⟩
  · rintro ⟨hf,hh⟩
    refine ⟨hf,(ForcingFormula.force_all hM hpre hp _ _).mpr ?_⟩
    intro x hx
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hxd r hr hrq
    obtain ⟨s,hs,hsr,y,hy,hxy,hym⟩ := hh x hx q hq hqp hxd r hr hrq
    exact ⟨s,hs,hsr,y,hy,(ForcingRelationClass.edge_formula hM hpre hs _ (0 : Fin 4) 2 3).mpr hxy,hym⟩
end Logic

/-- Pointwise stabilizers preserve both membership and nonmembership. -/
theorem perm_mem_iff {I J pi j image : M.Carrier .set}
    (hpi : ForcingConditionGraphs.Permutation I pi) (hf : ForcingLabelPermutations.Fixes J pi)
    (he : PureKuratowski.PairMember M j image pi) :
    (Project.FirstOrderSemantics.reduct M).mem image J ↔ (Project.FirstOrderSemantics.reduct M).mem j J := by
  constructor
  · intro him
    have e := hpi.2.1 j image image he (hf image him)
    exact e.symm ▸ him
  · intro hj
    have e := ForcingConditionGraphs.function_unique hpi.1.1 he (hf j hj)
    exact e.symm ▸ hj

/-- The internal index set I minus J, obtained by native Separation. -/
def OutsideIndex (I J O : M.Carrier .set) : Prop :=
  ∀ j, (Project.FirstOrderSemantics.reduct M).mem j O ↔
    (Project.FirstOrderSemantics.reduct M).mem j I ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem j J

theorem exists_outside_index (hM : FirstOrder.Theory.Models M nativeZF) (I J : M.Carrier .set) :
    ∃ O, OutsideIndex (M := M) I J O := by
  let query : Formula 2 := (Formula.mem 1 0).neg
  have sep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨O,hO⟩ := sep (fun _ => J) I
  refine ⟨O,?_⟩
  intro j
  exact hO j

/-- Literal collectRaw labels outside J; using the exact separated index is
extensionally the same collector as the source predicate j notin J at top. -/
def Outside (W I K c top bit J name : M.Carrier .set) : Prop :=
  ∃ O, OutsideIndex I J O ∧ ForcingLabelSet.LabelSet W O K c top bit name

theorem exists_outside (hM : FirstOrder.Theory.Models M nativeZF)
    {W K c top : M.Carrier .set} (hc : ForcingConditionGraphs.FunctionOn K c)
    (htW : (Project.FirstOrderSemantics.reduct M).mem top W) (I bit J : M.Carrier .set) :
    ∃ name, Outside (M := M) W I K c top bit J name := by
  obtain ⟨O,hO⟩ := exists_outside_index hM I J
  obtain ⟨name,hn⟩ := ForcingLabelSet.exists_labelSet hM hc htW O bit
  exact ⟨name,O,hO,hn⟩

/-- The exact raw edge condition, including absence from the fixed support. -/
theorem edge_outside (hM : FirstOrder.Theory.Models M nativeZF)
    {W I K c top bit J name child p : M.Carrier .set}
    (hn : Outside W I K c top bit J name) :
    PureKuratowski.PairMember M child p name ↔ p = top ∧
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j I ∧
        ¬ (Project.FirstOrderSemantics.reduct M).mem j J ∧ ForcingLabelNames.Label W K c top j bit child := by
  obtain ⟨O,hO,hn⟩ := hn
  rw [ForcingLabelSet.edge_labelSet hM hn]
  constructor
  · rintro ⟨hpt,j,hj,hl⟩
    exact ⟨hpt,j,((hO j).mp hj).1,((hO j).mp hj).2,hl⟩
  · rintro ⟨hpt,j,hj,hjJ,hl⟩
    exact ⟨hpt,j,(hO j).mpr ⟨hj,hjJ⟩,hl⟩

/-- The same outside collector is HS and fixed by the actual pointwise
stabilizer of J. No support membership or fixedness oracle is supplied. -/
theorem outside_HS_and_fixed (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w mu G F c top bit J fixing name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hNormal : ForcingNormalFilter.Normal I G F)
    (hFilter : ForcingSupportFilter.Filter I G mu F)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty top)
    (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I) (hJ : ForcingSupportSize.Small J mu)
    (hFix : ForcingLabelPermutations.Fixing G J fixing)
    (hn : Outside (v 6) I K c top bit J name) :
    HS actionFormula v G (v 6) F name ∧ ForcingSupportedNames.Supported v fixing name := by
  obtain ⟨O,hO,hn⟩ := hn
  obtain ⟨f,hf⟩ := ForcingLabelSet.exists_family hM hc (v 6) O top bit
  have htW := (hp.2.2.2.2.2 top).mpr (Or.inl ht)
  have hSub := ForcingConjugationGraph.fixing_subgroup hM hG hFix hJI
  have hHF := (hFilter fixing).mpr ⟨hSub,J,fixing,hJI,hJ,hFix,fun _ h => h⟩
  have hFamily : ForcingCollectedHS.FamilyHS v G (v 6) F O f := by
    intro j child hj hjc
    exact ForcingLabelNames.label_HS hM v hp hG hNormal hFilter hw hSmall hc ht ((hO j).mp hj).1
      ((hf.2 j child).mp hjc).2
  have hIndex : ForcingCollectedHS.IndexedPermutes ForcingLabelSet.topPredicate (fun _ : Fin 1 => top)
      v fixing O f (v 6) := by
    intro g hg A hga j child p hj hjc _ htop
    have ep := (ForcingLabelSet.topPredicate_semantics top j p).mp htop
    subst p
    have hg' := (hFix g).mp hg
    have hpi := (hG g).mp hg'.1
    have hjI := ((hO j).mp hj).1
    obtain ⟨i,hji,_⟩ := hpi.1.1.2 j hjI
    have hiI := hpi.1.2 j i hji
    have hiO := (hO i).mpr ⟨hiI,fun hiJ => ((hO j).mp hj).2 ((perm_mem_iff hpi hg'.2 hji).mp hiJ)⟩
    obtain ⟨image,hImage,_⟩ := hf.1.2 i hiO
    have hA := (mapRel_action v g A).mp hga
    exact ⟨i,image,top,hiO,hImage,(ForcingLabelSet.topPredicate_semantics top i top).mpr rfl,
      ForcingLabelNames.label_move hM v hp ht hpi hA hji
        ((hf.2 j child).mp hjc).2 ((hf.2 i image).mp hImage).2,
      ForcingProductFamily.top_fixed hp ht hA⟩
  have hperm := (ForcingCollectedHS.indexed_permutes_iff hM ForcingLabelSet.topPredicate (fun _ : Fin 1 => top) v fixing O f).mp hIndex
  have hCollected := (ForcingLabelSet.collected_iff hf htW).mpr hn
  exact ⟨ForcingCollectedHS.collect_HS hM ForcingLabelSet.topPredicate (fun _ : Fin 1 => top) v
    hp hG hNormal hSub hHF hFamily hperm hCollected,
    fun g hg A hA => ForcingCollectedHS.fixed hM ForcingLabelSet.topPredicate (fun _ : Fin 1 => top) v
      hp hG hSub hFamily hperm hCollected hg hA⟩

/-- Source mem_labelOutside, with all internal name candidates. -/
theorem mem_outside (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    {W I K c top bit J name nu p : M.Carrier .set}
    (hn : Outside W I K c top bit J name)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p W)
    (htW : (Project.FirstOrderSemantics.reduct M).mem top W)
    (hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q top) :
    Forces false R env W nu name p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q p →
        ∃ r j label, (Project.FirstOrderSemantics.reduct M).mem r W ∧ MapRel R env r q ∧
          (Project.FirstOrderSemantics.reduct M).mem j I ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem j J ∧
            ForcingLabelNames.Label W K c top j bit label ∧ Forces true R env W nu label r := by
  obtain ⟨O,hO,hn⟩ := hn
  rw [ForcingLabelDensity.mem_labelSet hM R env hn hp htW hTop]
  constructor
  · intro h q hq hqp
    obtain ⟨r,j,label,hr,hrq,hj,hl,he⟩ := h q hq hqp
    exact ⟨r,j,label,hr,hrq,((hO j).mp hj).1,((hO j).mp hj).2,hl,he⟩
  · intro h q hq hqp
    obtain ⟨r,j,label,hr,hrq,hj,hjJ,hl,he⟩ := h q hq hqp
    exact ⟨r,j,label,hr,hrq,(hO j).mpr ⟨hj,hjJ⟩,hl,he⟩

private def FamilyMembership {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (A family : M.Carrier .set) : Prop :=
  ∀ nu, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu →
        ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
          (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu family p ↔
            ForcingPowerName.SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p nu A ∧
            ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q p →
              ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env r q ∧
                ∃ x, Predicate (domain rho G F) env x ∧ Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x nu r)

/-- Actual Power Set followed by the actual nonempty Separation. Quantified
candidate subsets have no external rank bound. -/
private theorem exists_failure_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w A : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3))
      (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hNormal : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) A) :
    ∃ family, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) family ∧
      FamilyMembership env rho G F mul A family := by
  obtain ⟨bound,power,hBound,hPower,hRawPower⟩ := ForcingPowerAxiom.exists_at_value hM env rho G F mul hp hG hNormal hpre hA
  obtain ⟨family,hFamily,hSeparated⟩ := ForcingSeparationAxiom.exists_at_values hM env rho G F mul hp hG hNormal
    hPower (Fin.elim0 : Fin 0 → M.Carrier .set) (fun i => Fin.elim0 i) (Source.SetLanguage.nonempty 0)
  refine ⟨family,hFamily,?_⟩
  intro nu hnu p hpW
  rw [ForcingSeparationAxiom.mem_separate hM hpre hSeparated hpW,
    ForcingPowerName.mem_power hM env rho G F mul hp hG hNormal hpre hA hnu hBound hRawPower hpW]
  have ne := forces_nonempty hM (H := domain rho G F) hpre hpW (args1 nu) 0
  exact and_congr Iff.rfl ne

/-- Every member of the actual counterexample family is internally nonempty. -/
private theorem family_members_nonempty (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {env : Fin k → M.Carrier .set} {rho : Fin 7 → Fin k} {G F mul : Fin k}
    {A family p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hFamily : FamilyMembership env rho G F mul A family) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 family) (env (rho 6)) p
      (.all ((Formula.mem 1 0).imp (Source.SetLanguage.nonempty 1))) := by
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro nu hnu
  apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
  intro q hq hqp hm
  apply (forces_nonempty hM hpre hq _ _).mpr
  exact ((hFamily nu ((domain_semantics env rho G F nu).mp hnu) q hq).mp hm).2

/-- The literal outside-label name is a forced subset of the full label set. -/
theorem outside_subset (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    {W I K c top bit J name labels p : M.Carrier .set}
    (hn : Outside W I K c top bit J name) (hLabels : ForcingLabelSet.LabelSet W I K c top bit labels)
    (htW : (Project.FirstOrderSemantics.reduct M).mem top W)
    (hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q top) :
    ForcingPowerName.SubsetF R H env W p name labels := by
  intro nu _ q hq _ hm
  apply (ForcingLabelDensity.mem_labelSet hM R env hLabels hq htW hTop).mpr
  intro r hr hrq
  obtain ⟨s,j,label,hs,hsr,hj,_,hl,he⟩ := (mem_outside hM R env hn hq htW hTop).mp hm r hr hrq
  exact ⟨s,j,label,hs,hsr,hj,hl,he⟩

/-- Every actual outside label belongs to the literal collector at all conditions. -/
theorem label_mem_outside (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set}
    {W I K c top bit J name j label p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env W)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p W)
    (htW : (Project.FirstOrderSemantics.reduct M).mem top W) (hpt : MapRel R env p top)
    (hn : Outside W I K c top bit J name)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j I) (hjJ : ¬ (Project.FirstOrderSemantics.reduct M).mem j J)
    (hl : ForcingLabelNames.Label W K c top j bit label) : Forces false R env W label name p := by
  exact ForcingAtomicBasic.mem_of_edge_eq hM hpre htW hpt
    ((edge_outside hM hn).mpr ⟨rfl,j,hj,hjJ,hl⟩) (ForcingAtomicBasic.eq_refl hM hpre label p hp)

/-- Fixed ChoiceFailure.not_choiceOn on the SAME concrete system. -/
private theorem not_choiceOn_core (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin 40 → M.Carrier .set) (hCore : ForcingConcreteSystem.Core hM env)
    {family f p : M.Carrier .set}
    (hFamily : FamilyMembership env ForcingConcreteSystem.forcingRho 34 35 18 (env 37) family)
    (hf : HS actionFormula (fun j => env (ForcingConcreteSystem.forcingRho j)) (env 34) (env 33) (env 35) f)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env 33)) :
    ¬ Force (orderFormula (ForcingConcreteSystem.forcingRho 0) 18) (domain ForcingConcreteSystem.forcingRho 34 35)
      env (args2 f family) (env 33) p (Source.SetLanguage.choiceOn 0 1) := by
  let rho := ForcingConcreteSystem.forcingRho
  let v : Fin 7 → M.Carrier .set := fun j => env (rho j)
  let R := orderFormula (rho 0) 18
  let Hdom := domain rho 34 35
  obtain ⟨_,hm,_,hpres,hG,hFilter,hw,hMu,hI,hD,hMergers,hRow,hc,hEmpty,hLabels,_,_,hMark,hCard,hK,hCoding,hLo,hHi,_,hBits,_,_,_,_,_,_,_,_,_,_,hCoords,hSpace⟩ := hCore
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hSmallW := (ForcingSupportSize.native_small hM (env 39) (env 13)).mpr hMu.2
  have hLarge : ¬ ForcingSupportSize.Small (env 27) (env 13) := fun h =>
    hI.not_cardinalLessOrEqual (ZF.modelsKP hZF) ((ForcingSupportSize.native_small hM _ _).mp h)
  have hpre := ForcingProductPoset.preorder env (rho 0) 18 (rho 6) hm hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have htW := (hpres.2.2.2.2.2 (env 1)).mpr (Or.inl hEmpty)
  have hTop (z : M.Carrier .set) (_ : (Project.FirstOrderSemantics.reduct M).mem z (env 33)) : MapRel R env z (env 1) :=
    (ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 z (env 1)).mpr (Or.inl hEmpty)
  intro hchoice
  have hchoice := (forces_choiceOn hM hpre hpW (args2 f family) 0 1).mp hchoice
  obtain ⟨stabilizer,hStabilizer,hStabilizerF⟩ := ForcingHS.symmetric_of_hs hf
  obtain ⟨_,J,HJ,hJI,hJSmall,hFixJ,hIncluded⟩ := (hFilter stabilizer).mp hStabilizerF
  have hfSupport : ForcingSupportedNames.Supported v HJ f := by
    intro pi hpi ac hac
    obtain ⟨a,ha,hFixed⟩ := ((hStabilizer pi).mp (hIncluded pi hpi)).2
    have he := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp ha) ((mapRel_action _ _ _).mp hac)
    exact he ▸ hFixed
  obtain ⟨seed,hSeed⟩ := ConstructionDiagramAmalgamation.whole_embedding hM hMu.1 hI hD
  obtain ⟨d0,root,z0,hd0,hRoot,hz0,hz0p⟩ := ForcingLabelDensity.exists_condition_below hM hpres hm hSeed hpW
  have hz0W := ForcingSupportingRoot.code_mem hpres hd0 hRoot hz0
  obtain ⟨r,hr,hSub,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env 20) hMark) hRoot hJI hJSmall
  obtain ⟨A,hRange,hAI,hASmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hr hD
  obtain ⟨HA,hFixA⟩ := ForcingLabelPermutations.exists_fixing hM (env 34) A
  have hJA : (Project.FirstOrderSemantics.reduct M).MemberSubset J A := fun x hx => (hRange x).mpr (hCover x hx)
  have hfA := ForcingSupportedNames.supported_mono hFixJ hFixA hJA hfSupport
  obtain ⟨q,hqCode⟩ := ForcingSupportingRoot.exists_code hM d0 r
  have hqW := ForcingSupportingRoot.code_mem hpres hd0 hr hqCode
  have hqz0 : MapRel R env q z0 := (ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 q z0).mpr
    ((ForcingSupportingRoot.code_le hqCode hz0).mpr ⟨fun _ h => h,env 20,hMark,hSub⟩)
  have hqp : MapRel R env q p := hpre.2 q z0 p hqW hz0W hpW hqz0
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 z0 p).mpr hz0p)
  obtain ⟨outside,hOutside⟩ := exists_outside hM hc htW (env 27) (env 2) A
  have hOutsideData := outside_HS_and_fixed hM v hpres hG hNormal hFilter hw hSmallW hc hEmpty hAI hASmall hFixA hOutside
  have outside_member (z : M.Carrier .set) (hz : (Project.FirstOrderSemantics.reduct M).mem z (env 33)) :
      Forces false R env (env 33) outside family z := by
    apply (hFamily outside hOutsideData.1 z hz).mpr
    refine ⟨outside_subset hM R Hdom env hOutside hLabels htW hTop,?_⟩
    have hExists : ∃ j, (Project.FirstOrderSemantics.reduct M).mem j (env 27) ∧
        ¬ (Project.FirstOrderSemantics.reduct M).mem j A := by
      apply Classical.byContradiction
      intro hn
      have hIA : (Project.FirstOrderSemantics.reduct M).MemberSubset (env 27) A := by
        intro j hj
        exact Classical.byContradiction (fun hnA => hn ⟨j,hj,hnA⟩)
      exact hLarge (ForcingSupportSize.small_subset hM hIA hASmall)
    obtain ⟨j,hj,hjA⟩ := hExists
    obtain ⟨label,hLabel⟩ := ForcingLabelNames.exists_label hM hc (env 33) (env 1) j (env 2)
    have hLabelHS := ForcingLabelNames.label_HS hM v hpres hG hNormal hFilter hw hSmallW hc hEmpty hj hLabel
    intro t htW' _
    exact ⟨t,htW',hpre.1 t htW',label,(domain_semantics env rho 34 35 label).mpr hLabelHS,
      label_mem_outside hM hpre htW' htW (hTop t htW') hOutside hj hjA hLabel⟩
  obtain ⟨s,hs,hsq,y,hy,hApp,hyOut⟩ := hchoice.2 outside
    ((domain_semantics env rho 34 35 outside).mpr hOutsideData.1) q hqW hqp (outside_member q hqW) q hqW (hpre.1 q hqW)
  obtain ⟨s',j,label,hs',hs's,hj,hjA,hLabel,hyLabel⟩ := (mem_outside hM R env hOutside hs htW hTop).mp hyOut s hs (hpre.1 s hs)
  have hApp' : Force R Hdom env (args3 f outside label) (env 33) s' (Source.SetLanguage.edge 0 1 2) := by
    apply (ForcingFormula.tuple_congr hM (H := Hdom) hpre (Source.SetLanguage.edge 0 1 2)
      (args3 f outside y) (args3 f outside label) s' hs' ?_).mp
    · exact ForcingFormula.mono hM hpre _ _ hs hs' hs's hApp
    · intro i
      exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre f s' hs')
        (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre outside s' hs') (Fin.cases hyLabel (fun i => Fin.elim0 i))) i
  obtain ⟨d1,t0,z1,hd1,ht0,hz1,hz1s⟩ := ForcingLabelDensity.exists_condition_below hM hpres hm hSeed hs'
  obtain ⟨single,hSingle⟩ := ForcingWithTopCarrier.exists_single hM j
  have hSingleI : (Project.FirstOrderSemantics.reduct M).MemberSubset single (env 27) :=
    fun x hx => ((hSingle x).mp hx).symm ▸ hj
  obtain ⟨t,ht,hSubT,hCoverT⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env 20) hMark) ht0 hSingleI (ForcingLabelNames.singleton_small hM hw hSmallW hSingle)
  obtain ⟨d,hdCode⟩ := ForcingSupportingRoot.exists_code hM d1 t
  have hdW := ForcingSupportingRoot.code_mem hpres hd1 ht hdCode
  have hz1W := ForcingSupportingRoot.code_mem hpres hd1 ht0 hz1
  have hdz1 : MapRel R env d z1 := (ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 d z1).mpr
    ((ForcingSupportingRoot.code_le hdCode hz1).mpr ⟨fun _ h => h,env 20,hMark,hSubT⟩)
  have hds : MapRel R env d s' := hpre.2 d z1 s' hdW hz1W hs' hdz1
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 z1 s').mpr hz1s)
  have hdq : MapRel R env d q := hpre.2 d s q hdW hs hqW (hpre.2 d s' s hdW hs' hs hds hs's) hsq
  have htr := ((ForcingSupportingRoot.code_le hdCode hqCode).mp
    ((ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 d q).mp hdq)).2
  have hjt := hCoverT j ((hSingle j).mpr rfl)
  have hdApp := ForcingFormula.mono hM hpre _ _ hs' hdW hds hApp'
  obtain ⟨dR,_,hRestr,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd1 A
  have hCompat : ConstructionCohenCompatibility.Compatible dR dR := by
    intro x y z hxy hxz
    exact hd1.2.1 x y z (by obtain ⟨a,ha,hm⟩ := hxy; exact ⟨a,ha,((hRestr a).mp hm).1⟩)
      (by obtain ⟨a,ha,hm⟩ := hxz; exact ⟨a,ha,((hRestr a).mp hm).1⟩)
  obtain ⟨pi,rawV,hpi,hFixRange,tP,dP,a,u,c0,c1,htP,hPiT,hInter,hMoved,ha,hu,hRawV,hc0,hc1,hv0,hv1⟩ :=
    ConstructionCompatiblePlacement.compatible_placement hM hChoice hw hMu hI hD hMergers hRow hm
      ⟨hCoords,hSpace,hr,ht,ht,htr,htr,hd1,hd1,A,dR,dR,hRange,hRestr,hRestr,hCompat⟩
  have hpiHA : (Project.FirstOrderSemantics.reduct M).mem pi HA :=
    (hFixA pi).mpr ⟨(hG pi).mpr hpi,fun x hx => hFixRange x ((hRange x).mp hx)⟩
  obtain ⟨jP,hjPedge,_⟩ := hpi.1.1.2 j hj
  have hjP := hpi.1.2 j jP hjPedge
  have hjNe : j ≠ jP := by
    intro e
    have hjTP : ConstructionPlacementTriple.ImageAt tP (env (rho 0)) j := by
      obtain ⟨x,hx,hxj⟩ := hjt
      exact ⟨x,hx,(hPiT x j).mpr ⟨hx,j,hxj,e.symm ▸ hjPedge⟩⟩
    exact hjA ((hRange j).mpr ((hInter j).mp ⟨hjt,hjTP⟩))
  obtain ⟨labelP,hLabelP⟩ := ForcingLabelNames.exists_label hM hc (env 33) (env 1) jP (env 2)
  obtain ⟨action,hAction⟩ := ForcingProductFamily.exists_action hM hpres hpi
  have hActionRel := (mapRel_action v pi action).mpr hAction
  obtain ⟨dMoved,hdMovedCode⟩ := ForcingSupportingRoot.exists_code hM dP tP
  have hdP := (ConstructionDescentPlacement.actual_moved_condition hMoved).1
  have hdMovedW := ForcingSupportingRoot.code_mem hpres hdP htP hdMovedCode
  have hMovedApp : Force R Hdom env (args3 f outside labelP) (env 33) dMoved (Source.SetLanguage.edge 0 1 2) := by
    apply (ForcingSeparation.symmetry hM env rho 34 35 18 hpres hG hNormal hpi hActionRel
      (Source.SetLanguage.edge 0 1 2) (args3 f outside label) (args3 f outside labelP) ?_ hdW
      (ForcingSupportingRoot.moved_code hM hpres hAction hd1 ht htP hMoved hPiT hdCode hdMovedCode)).mp hdApp
    intro i
    exact Fin.cases (hfA pi hpiHA action hActionRel)
      (Fin.cases (hOutsideData.2 pi hpiHA action hActionRel)
        (Fin.cases (ForcingLabelNames.label_move hM v hpres hEmpty hpi hAction hjPedge hLabel hLabelP) (fun i => Fin.elim0 i))) i
  obtain ⟨zV,hzV⟩ := ForcingSupportingRoot.exists_code hM a u
  have hzVW := ForcingSupportingRoot.code_mem hpres ha hu hzV
  have hzVd : MapRel R env zV d := by
    obtain ⟨cv,hcv,hcvSingle⟩ := hzV
    obtain ⟨cd,hcd,hcdSingle⟩ := hdCode
    have ev := KuratowskiZF.code_unique hM hcv hRawV
    have ed := KuratowskiZF.code_unique hM hc0 hcd
    exact (ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 zV d).mpr
      (Or.inr ⟨cv,cd,hcvSingle,hcdSingle,ev.symm ▸ ed ▸ hv0⟩)
  have hzVP : MapRel R env zV dMoved := by
    obtain ⟨cv,hcv,hcvSingle⟩ := hzV
    obtain ⟨cd,hcd,hcdSingle⟩ := hdMovedCode
    have ev := KuratowskiZF.code_unique hM hcv hRawV
    have ed := KuratowskiZF.code_unique hM hc1 hcd
    exact (ForcingProductSymmetry.orderFormula_semantics env (rho 0) 18 zV dMoved).mpr
      (Or.inr ⟨cv,cd,hcvSingle,hcdSingle,ev.symm ▸ ed ▸ hv1⟩)
  have hzVp := hpre.2 zV q p hzVW hqW hpW (hpre.2 zV d q hzVW hdW hqW hzVd hdq) hqp
  have hLabelHS := ForcingLabelNames.label_HS hM v hpres hG hNormal hFilter hw hSmallW hc hEmpty hj hLabel
  have hLabelPHS := ForcingLabelNames.label_HS hM v hpres hG hNormal hFilter hw hSmallW hc hEmpty hjP hLabelP
  have hEqual := functionOn_unique hM hpre hzVW (args2 f family) 0 1
    (ForcingFormula.mono hM hpre _ _ hpW hzVW hzVp hchoice.1)
    ((domain_semantics env rho 34 35 outside).mpr hOutsideData.1)
    ((domain_semantics env rho 34 35 label).mpr hLabelHS)
    ((domain_semantics env rho 34 35 labelP).mpr hLabelPHS)
    (outside_member zV hzVW)
    (ForcingFormula.mono hM hpre _ _ hdW hzVW hzVd hdApp)
    (ForcingFormula.mono hM hpre _ _ hdMovedW hzVW hzVP hMovedApp)
  exact ForcingLabelSeparation.label_not_equal hM env rho 18 hpres hm hw hK hCoding hEmpty hLo hHi hBits hSeed hj hjP hjNe hLabel hLabelP hEqual

/-- Source forces_not_AC for every condition of the SAME actual system. -/
theorem on_core (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin 40 → M.Carrier .set) (hCore : ForcingConcreteSystem.Core hM env) :
    ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env 33) →
      Force (orderFormula (ForcingConcreteSystem.forcingRho 0) 18) (domain ForcingConcreteSystem.forcingRho 34 35)
        env Fin.elim0 (env 33) p Source.SetLanguage.AC.neg := by
  let rho := ForcingConcreteSystem.forcingRho
  have hData := hCore
  obtain ⟨_,hm,_,hpres,hG,hFilter,hw,hMu,_,_,_,_,hc,ht,hLabels,_⟩ := hData
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hSmall := (ForcingSupportSize.native_small hM (env 39) (env 13)).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j))
    hpres hG hNormal hFilter hw hSmall hc ht hLabels).1
  have hpre := ForcingProductPoset.preorder env (rho 0) 18 (rho 6) hm hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  obtain ⟨family,hFamilyHS,hFamily⟩ := exists_failure_family hM env rho 34 35 18 hpres hG hNormal hpre hA
  intro p hpW
  apply (ForcingFormula.force_neg hM hpre hpW Fin.elim0 Source.SetLanguage.AC).mpr
  intro q hq hqp hAC
  rw [Source.SetLanguage.AC] at hAC
  have hh := (ForcingFormula.force_all hM hpre hq _ _).mp hAC family
    ((domain_semantics env rho 34 35 family).mpr hFamilyHS)
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq)
    (family_members_nonempty hM hpre hq hFamily)
  obtain ⟨r,hr,_,f,hf,hChoiceOn⟩ := hh q hq (hpre.1 q hq)
  apply not_choiceOn_core hM hChoice env hCore hFamily ((domain_semantics env rho 34 35 f).mp hf) hr
  change Force (orderFormula (rho 0) 18) (domain rho 34 35) env
    (Fin.lastCases f (Fin.lastCases family Fin.elim0)) (env (rho 6)) r (Source.SetLanguage.choiceOn 1 0) at hChoiceOn
  change Force (orderFormula (rho 0) 18) (domain rho 34 35) env
    (args2 f family) (env (rho 6)) r (Source.SetLanguage.choiceOn 0 1)
  rw [Source.SetLanguage.choiceOn,ForcingSound.rename hM hpre _ _ _ _ hr] at hChoiceOn ⊢
  exact hChoiceOn

/-- Original object formula: the product interpretation forces non-Choice at
all internal original conditions, with no name rank cutoff. -/
def outcomeFormula : Project.Formula 1 40 :=
  .forallE (.imp (.mem (.bound 0) (.bound (33 : Fin 40).succ))
    (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (ForcingConcreteSystem.forcingRho 0) 18)
      (domain ForcingConcreteSystem.forcingRho 34 35) Fin.succ Fin.elim0 (33 : Fin 40).succ 0 Source.SetLanguage.AC.neg)))

theorem outcomeFormula_freeClosed : outcomeFormula.FreeClosed := by
  simp -implicitDefEqProofs [outcomeFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem outcomeFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 40) :
    Project.Formula.satisfies env outcomeFormula ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound 33) →
        Force (orderFormula (ForcingConcreteSystem.forcingRho 0) 18) (domain ForcingConcreteSystem.forcingRho 34 35)
          env.bound Fin.elim0 (env.bound 33) p Source.SetLanguage.AC.neg := by
  simp only [outcomeFormula,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingFormula.formula_semantics,id_eq]
  rfl

def sentence : Project.Sentence where
  formula := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj ForcingConcreteSystem.coreFormula (.conj ForcingConcreteSystem.outcomeFormula (.conj ForcingNonwellorderableImage.imageOutcomeFormula outcomeFormula)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ForcingConcreteSystem.coreFormula_freeClosed,ForcingConcreteSystem.outcomeFormula_freeClosed,ForcingNonwellorderableImage.imageOutcomeFormula_freeClosed,outcomeFormula_freeClosed]

theorem models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence sentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) sentence.formula
  obtain ⟨w,hw⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome⟩ := ForcingConcreteSystem.construct hM hOrder hChoice hw
  have hImages := ForcingNonwellorderableImage.on_core hM _ hCore hOutcome
  have hNotChoice := on_core hM hChoice _ hCore
  simp only [sentence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingConcreteSystem.coreFormula_semantics hM,ForcingConcreteSystem.outcomeFormula_semantics hM,ForcingNonwellorderableImage.imageOutcomeFormula_semantics hM,outcomeFormula_semantics hM]
  exact ⟨w,bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome,hImages,hNotChoice⟩

theorem kernel_certificate :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sentence))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sentence)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sentence)).mp
      (models hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ForcingChoiceFailure
