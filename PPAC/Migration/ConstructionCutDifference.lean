/- Nonnegative differences of arbitrary internal cuts, as required by the
pinned ProbeMargins.exists_letter_interval. The value is an exact separated
set of rational gaps; addition recovery is proved, not postulated. -/
import PPAC.Migration.ConstructionCutLocatedness

namespace PPAC.Migration.ConstructionCutDifference
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
open ConstructionCutAddition (SumMember SumCut AddBound)
open ConstructionCutAssociativity (sum_fraction)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def GapMember (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b q : M.Carrier .set) : Prop :=
  ∃ u r, (Project.FirstOrderSemantics.reduct M).mem u Q ∧
    ¬ (Project.FirstOrderSemantics.reduct M).mem u a ∧ Sum hM w u q r ∧
    (Project.FirstOrderSemantics.reduct M).mem r b

def Value (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b gap : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q gap ↔
    (Project.FirstOrderSemantics.reduct M).mem q Q ∧ GapMember hM w Q a b q

def gapMember {m : Nat} (w Q a b q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (.mem (.bound 1) (.bound Q.succ.succ))
    (.conj (.neg (.mem (.bound 1) (.bound a.succ.succ)))
      (.conj (ConstructionFractionAddition.sum w.succ.succ 1 q.succ.succ 0)
        (.mem (.bound 0) (.bound b.succ.succ))))))

theorem gapMember_freeClosed {m : Nat} (w Q a b q : Fin m) : (gapMember w Q a b q).FreeClosed := by
  simp -implicitDefEqProofs [gapMember,Definitional.Formula.FreeClosed,ConstructionFractionAddition.sum_freeClosed]

theorem gapMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q a b q : Fin m) :
    Project.Formula.satisfies env (gapMember w Q a b q) ↔
      GapMember hM (env.bound w) (env.bound Q) (env.bound a) (env.bound b) (env.bound q) := by
  simp only [gapMember,GapMember,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    ConstructionFractionAddition.sum_semantics hM]
  rfl

def value {m : Nat} (w Q a b gap : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound gap.succ))
    (.conj (.mem (.bound 0) (.bound Q.succ)) (gapMember w.succ Q.succ a.succ b.succ 0)))

theorem value_freeClosed {m : Nat} (w Q a b gap : Fin m) : (value w Q a b gap).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,gapMember_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q a b gap : Fin m) :
    Project.Formula.satisfies env (value w Q a b gap) ↔
      Value hM (env.bound w) (env.bound Q) (env.bound a) (env.bound b) (env.bound gap) := by
  simp only [value,Value,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,gapMember_semantics hM]
  rfl

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b : M.Carrier .set) :
    ∃ gap, Value hM w Q a b gap := by
  let schema : Project.UnarySchema 4 := {
    body := gapMember 1 2 3 4 0
    freeClosed := gapMember_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases a (fun _ => b))), free := fun _ => w }
  obtain ⟨gap,hgap⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  exact ⟨gap,fun q => (hgap q).trans (and_congr_right (fun _ => gapMember_semantics hM (env.push q) 1 2 3 4 0))⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b gap gap' : M.Carrier .set}
    (hg : Value hM w Q a b gap) (hg' : Value hM w Q a b gap') : gap = gap' :=
  (ModelTransfer.extensionality hM).eq_of_same_members gap gap' (fun q => (hg q).trans (hg' q).symm)

theorem gap_subset (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b gap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hb : Cut hM w Q b)
    (hg : Value hM w Q a b gap) : Subset gap b := by
  intro q hq
  obtain ⟨_,u,r,_,_,hs,hr⟩ := (hg q).mp hq
  exact hb.2.1 q r hr (ConstructionBasePointBound.sum_right_le hM hw hs)

theorem value_cut (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b gap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hb : Cut hM w Q b) (hg : Value hM w Q a b gap) : Cut hM w Q gap := by
  refine ⟨fun q hq => ((hg q).mp hq).1,?_,?_,?_⟩
  · intro q p hp hqp
    obtain ⟨_,u,r,hu,hnu,hs,hr⟩ := (hg p).mp hp
    have hqpCopy := hqp
    obtain ⟨i,j,_,_,hq,_,_⟩ := hqpCopy
    obtain ⟨t,ht⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ u).mp hu) ⟨i,j,hq⟩
    have htr := (ConstructionFractionAddition.sum_left_le_iff hM hw ht hs).mpr hqp
    exact (hg q).mpr ⟨(hQ q).mpr ⟨i,j,hq⟩,u,t,hu,hnu,ht,hb.2.1 t r hr htr⟩
  · intro q hq
    obtain ⟨_,u,r,hu,hnu,hs,hr⟩ := (hg q).mp hq
    obtain ⟨r',hr',hrr'⟩ := hb.2.2.1 r hr
    have hur' := le_lt_trans hM hw (ConstructionBasePointBound.sum_left_le hM hw hs) hrr'
    obtain ⟨p,t,hp,ht,htr',hr't⟩ := ConstructionFractionDifference.difference_exists hM hw hur'.1
    have hrt := lt_le_trans hM hw hrr' hr't
    have hqp := (ConstructionFractionAddition.sum_right_lt_iff hM hw
      (ConstructionFractionAddition.sum_comm hM hw hs) (ConstructionFractionAddition.sum_comm hM hw ht)).mp hrt
    exact ⟨p,(hg p).mpr ⟨(hQ p).mpr hp,u,t,hu,hnu,ht,hb.2.1 t r' hr' htr'⟩,hqp⟩
  · obtain ⟨q,hq,hnq⟩ := hb.2.2.2
    exact ⟨q,hq,fun h => hnq (gap_subset hM hw hb hg q h)⟩

theorem addition_bound (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b gap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hab : Subset a b)
    (hg : Value hM w Q a b gap) : AddBound hM w a gap b := by
  intro p hp
  rcases hp with hp | hp | ⟨q,r,s,hq,hr,hs,hps⟩
  · exact hab p hp
  · exact gap_subset hM hw hb hg p hp
  · obtain ⟨_,u,t,hu,hnu,ht,htb⟩ := (hg r).mp hr
    have hqu := ConstructionCutArithmetic.below_omitted hM hw hQ ha hu hnu hq
    have hst := (ConstructionFractionAddition.sum_right_lt_iff hM hw hs ht).mpr hqu
    exact hb.2.1 p t htb (le_trans hM hw hps hst.1)

/-- Commuting the middle two summands follows from the accepted fraction
associativity and commutativity, retaining value equivalence. -/
theorem swap_summands (hM : FirstOrder.Theory.Models M nativeZF) {w a e g u t r v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hu : Sum hM w a e u) (ht : Sum hM w a g t)
    (hr : Sum hM w u g r) (hv : Sum hM w t e v) : Le hM w r v ∧ Le hM w v r := by
  have huCopy := hu
  obtain ⟨_,_,c,d,_,_,_,he,_,_⟩ := huCopy
  have htCopy := ht
  obtain ⟨i,j,k,l,_,_,ha,hg,_,_⟩ := htCopy
  obtain ⟨ge,hge⟩ := ConstructionFractionAddition.sum_exists hM hw ⟨k,l,hg⟩ ⟨c,d,he⟩
  obtain ⟨total,hTotal⟩ := ConstructionFractionAddition.sum_exists hM hw ⟨i,j,ha⟩ (sum_fraction hge)
  have eqR := ConstructionCutAssociativity.fraction_assoc hM hw hu
    (ConstructionFractionAddition.sum_comm hM hw hge) hr hTotal
  have eqV := ConstructionCutAssociativity.fraction_assoc hM hw ht hge hv hTotal
  exact ⟨le_trans hM hw eqR.1 eqV.2,le_trans hM hw eqV.1 eqR.2⟩

/-- An ordered strict fraction gap has a nonempty numerator. -/
theorem positive_difference (hM : FirstOrder.Theory.Models M nativeZF) {w p r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hpr : Lt hM w p r) :
    ∃ delta num den s, Coordinates w delta num den ∧
      (∃ x, (Project.FirstOrderSemantics.reduct M).mem x num) ∧ Sum hM w p delta s ∧
      Le hM w s r ∧ Le hM w r s := by
  obtain ⟨delta,s,hd,hs,hsr,hrs⟩ := ConstructionFractionDifference.difference_exists hM hw hpr.1
  obtain ⟨num,den,hd⟩ := hd
  have hp : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x num := by
    apply Classical.byContradiction
    intro hn
    obtain ⟨zero,hzero,hzw⟩ := hw.1.1
    obtain ⟨one,hOne,how⟩ := hw.1.2 zero hzw
    obtain ⟨z,hzCode⟩ := KuratowskiZF.exists_code hM zero one
    have hz : Coordinates w z zero one := ⟨hzw,how,⟨zero,hOne.predecessor_mem⟩,hzCode⟩
    have hdLe := ConstructionCutLocatedness.empty_le hM hw hd (fun x hx => hn ⟨x,hx⟩) ⟨zero,one,hz⟩
    have hprCopy := hpr.1
    obtain ⟨a,b,_,_,hp,_,_⟩ := hprCopy
    have hzeroSum := ConstructionFractionDifference.sum_zero hM hw ⟨a,b,hp⟩ hz hzero ⟨zero,hzero,hOne⟩
    have hsp := (ConstructionFractionAddition.sum_left_le_iff hM hw hs hzeroSum).mpr hdLe
    exact hpr.2 (le_trans hM hw hrs hsp)
  exact ⟨delta,num,den,s,hd,hp,hs,hsr,hrs⟩

/-- The reverse inclusion is the substantive subtraction law. It uses an
internal boundary approximation, not just a one-sided bound for a candidate. -/
theorem addition_recovers (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b gap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hab : Subset a b)
    (hg : Value hM w Q a b gap) : SumCut hM w Q a gap b := by
  classical
  intro p
  constructor
  · intro hpb
    refine ⟨hb.1 p hpb,?_⟩
    by_cases hpa : (Project.FirstOrderSemantics.reduct M).mem p a
    · exact Or.inl hpa
    · by_cases hNonempty : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q a
      · obtain ⟨p',hp'b,hpp'⟩ := hb.2.2.1 p hpb
        obtain ⟨delta,num,den,s,hd,hNum,hs,hsp',hp's⟩ := positive_difference hM hw hpp'
        obtain ⟨q,step,u,hqa,hnua,hu,hStep⟩ := ConstructionCutLocatedness.small_boundary hM hw hQ ha hNonempty hd hNum
        have hqp := ConstructionCutArithmetic.below_omitted hM hw hQ ha (hb.1 p hpb) hpa hqa
        obtain ⟨g,t,hgFrac,ht,htp,hpt⟩ := ConstructionFractionDifference.difference_exists hM hw hqp.1
        obtain ⟨r,hr⟩ := ConstructionFractionAddition.sum_exists hM hw (sum_fraction hu) hgFrac
        have huCopy := hu
        obtain ⟨_,_,stepNum,stepDen,_,_,_,hStepCoords,_,_⟩ := huCopy
        have hStepFrac : Fraction w step := ⟨stepNum,stepDen,hStepCoords⟩
        obtain ⟨v,hv⟩ := ConstructionFractionAddition.sum_exists hM hw (sum_fraction ht) hStepFrac
        obtain ⟨pe,hpe⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ p).mp (hb.1 p hpb)) hStepFrac
        have eqR := swap_summands hM hw hu ht hr hv
        have eqV := ConstructionFractionAddition.sum_equiv hM hw hv hpe ⟨htp,hpt⟩
          ⟨le_refl hM hw hStepFrac,le_refl hM hw hStepFrac⟩
        have hPeS := (ConstructionFractionAddition.sum_right_lt_iff hM hw
          (ConstructionFractionAddition.sum_comm hM hw hpe) (ConstructionFractionAddition.sum_comm hM hw hs)).mpr hStep
        have hrs := le_trans hM hw eqR.1 (le_trans hM hw eqV.1 hPeS.1)
        have hrb := hb.2.1 r p' hp'b (le_trans hM hw hrs hsp')
        have hggap := (hg g).mpr ⟨(hQ g).mpr hgFrac,u,r,(hQ u).mpr (sum_fraction hu),hnua,hr,hrb⟩
        exact Or.inr (Or.inr ⟨q,g,t,hqa,hggap,ht,hpt⟩)
      · obtain ⟨zero,hzero,hzw⟩ := hw.1.1
        obtain ⟨one,hOne,how⟩ := hw.1.2 zero hzw
        obtain ⟨z,hzCode⟩ := KuratowskiZF.exists_code hM zero one
        have hz : Coordinates w z zero one := ⟨hzw,how,⟨zero,hOne.predecessor_mem⟩,hzCode⟩
        have hzeroSum := ConstructionFractionDifference.sum_zero hM hw ((hQ p).mp (hb.1 p hpb)) hz hzero ⟨zero,hzero,hOne⟩
        have hpg := (hg p).mpr ⟨hb.1 p hpb,z,p,(hQ z).mpr ⟨zero,one,hz⟩,
          fun h => hNonempty ⟨z,h⟩,ConstructionFractionAddition.sum_comm hM hw hzeroSum,hpb⟩
        exact Or.inr (Or.inl hpg)
  · exact fun hp => addition_bound hM hw hQ ha hb hab hg p hp.2

theorem exists_difference (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hab : Subset a b) :
    ∃ gap, Cut hM w Q gap ∧ Value hM w Q a b gap ∧ SumCut hM w Q a gap b ∧
      (∀ g, Value hM w Q a b g → g = gap) ∧
      (¬ Subset b a → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p gap) := by
  obtain ⟨gap,hg⟩ := exists_value hM w Q a b
  have hSum := addition_recovers hM hw hQ ha hb hab hg
  refine ⟨gap,value_cut hM hw hQ hb hg,hg,hSum,fun _ h => value_unique hM h hg,?_⟩
  intro hStrict
  apply Classical.byContradiction
  intro hn
  have hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p gap := fun p hp => hn ⟨p,hp⟩
  have hIdentity := (ConstructionCutArithmetic.sum_zero hz ha).2
  have he := ConstructionCutAddition.sum_unique hM hSum hIdentity
  exact hStrict (he.symm ▸ (fun p hp => hp : Subset a a))

/-- Translation by any cut reflects inclusion, including the empty-cut case.
The separated internal grid prevents a nonzero difference being lost in a sum. -/
theorem sum_le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c ac bc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hac : SumCut hM w Q a c ac) (hbc : SumCut hM w Q b c bc) :
    Subset ac bc ↔ Subset a b := by
  classical
  constructor
  · intro hSub
    by_cases hNonempty : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q c
    · intro p hpa
      apply Classical.byContradiction
      intro hnpb
      obtain ⟨r,hra,hpr⟩ := ha.2.2.1 p hpa
      obtain ⟨delta,num,den,d,hd,hNum,hpd,hdr,hrd⟩ := positive_difference hM hw hpr
      obtain ⟨q,step,u,hqc,hnu,hqu,hStep⟩ := ConstructionCutLocatedness.small_boundary hM hw hQ hc hNonempty hd hNum
      obtain ⟨s,hrs⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ r).mp (ha.1 r hra)) ((hQ q).mp (hc.1 q hqc))
      have hsa := (hac s).mpr ⟨(hQ s).mpr (sum_fraction hrs),Or.inr (Or.inr
        ⟨r,q,s,hra,hqc,hrs,le_refl hM hw (sum_fraction hrs)⟩)⟩
      have hsb := ((hbc s).mp (hSub s hsa)).2
      rcases hsb with hsb | hsc | ⟨x,y,z,hxb,hyc,hxy,hsz⟩
      · exact hnpb (hb.2.1 p s hsb (le_trans hM hw hpr.1 (ConstructionBasePointBound.sum_left_le hM hw hrs)))
      · have hStepR := le_trans hM hw hStep.1
          (le_trans hM hw (ConstructionBasePointBound.sum_right_le hM hw hpd) hdr)
        have hus := (ConstructionFractionAddition.sum_left_le_iff hM hw hqu
          (ConstructionFractionAddition.sum_comm hM hw hrs)).mpr hStepR
        exact hnu (hc.2.1 u s hsc hus)
      · have hxp := (ConstructionCutArithmetic.below_omitted hM hw hQ hb (ha.1 p hpa) hnpb hxb).1
        have hyu := (ConstructionCutArithmetic.below_omitted hM hw hQ hc
          ((hQ u).mpr (sum_fraction hqu)) hnu hyc).1
        obtain ⟨pu,hpu⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ p).mp (ha.1 p hpa)) (sum_fraction hqu)
        have hzpu := ConstructionFractionAddition.sum_mono hM hw hxy hpu hxp hyu
        have hquCopy := hqu
        obtain ⟨_,_,i,j,_,_,_,hStepCoords,_,_⟩ := hquCopy
        obtain ⟨pe,hpe⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ p).mp (ha.1 p hpa)) ⟨i,j,hStepCoords⟩
        have hped := (ConstructionFractionAddition.sum_right_lt_iff hM hw
          (ConstructionFractionAddition.sum_comm hM hw hpe) (ConstructionFractionAddition.sum_comm hM hw hpd)).mpr hStep
        have hper := lt_le_trans hM hw hped hdr
        obtain ⟨peq,hpeq⟩ := ConstructionFractionAddition.sum_exists hM hw (sum_fraction hpe) ((hQ q).mp (hc.1 q hqc))
        have hpeqS := (ConstructionFractionAddition.sum_right_lt_iff hM hw hpeq hrs).mpr hper
        have he := ConstructionCutAssociativity.fraction_assoc hM hw hpe
          (ConstructionFractionAddition.sum_comm hM hw hqu) hpeq hpu
        have hpuS := le_lt_trans hM hw he.2 hpeqS
        exact hpuS.2 (le_trans hM hw hsz hzpu)
    · have hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p c := fun p hp => hNonempty ⟨p,hp⟩
      have heA := ConstructionCutAddition.sum_unique hM hac (ConstructionCutArithmetic.sum_zero hz ha).2
      have heB := ConstructionCutAddition.sum_unique hM hbc (ConstructionCutArithmetic.sum_zero hz hb).2
      exact heA ▸ heB ▸ hSub
  · exact fun h => ConstructionCutArithmetic.sum_mono hac hbc h (fun _ hp => hp)

theorem sum_cancel (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c ac bc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hac : SumCut hM w Q a c ac) (hbc : SumCut hM w Q b c bc) (he : ac = bc) : a = b := by
  have hAB := (sum_le_iff hM hw hQ ha hb hc hac hbc).mp (fun _ hp => he ▸ hp)
  have hBA := (sum_le_iff hM hw hQ hb ha hc hbc hac).mp (fun _ hp => he.symm ▸ hp)
  exact (ModelTransfer.extensionality hM).eq_of_same_members a b (fun p => ⟨hAB p,hBA p⟩)

/-- Uniqueness holds among all cut-valued solutions of the addition equation,
not just among sets satisfying the chosen gap-membership definition. -/
theorem difference_solution_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q a b g g' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hg : Cut hM w Q g) (hg' : Cut hM w Q g')
    (hs : SumCut hM w Q a g b) (hs' : SumCut hM w Q a g' b) : g = g' :=
  sum_cancel hM hw hQ hg hg' ha (ConstructionCutArithmetic.sum_comm hM hw hs)
    (ConstructionCutArithmetic.sum_comm hM hw hs') rfl

theorem sum_strict_iff (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c ac bc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hac : SumCut hM w Q a c ac) (hbc : SumCut hM w Q b c bc) :
    (Subset ac bc ∧ ¬ Subset bc ac) ↔ (Subset a b ∧ ¬ Subset b a) :=
  and_congr (sum_le_iff hM hw hQ ha hb hc hac hbc) (not_congr (sum_le_iff hM hw hQ hb ha hc hbc hac))

end PPAC.Migration.ConstructionCutDifference
