/- General nonnegative cut addition consumed by pinned ProbeMargins interval
and Word-height formulas. Reuse the accepted principal bound, bounded sum,
cartesian product and native definable-function graph constructors. -/
import PPAC.Migration.ConstructionBasePointBound

namespace PPAC.Migration.ConstructionCutArithmetic
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
open ConstructionCutAddition (SumMember SumCut)
open ConstructionProbeLetters (Representatives)
open ForcingDiagramOrder (Product)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem below_omitted (hM : FirstOrder.Theory.Models M nativeZF) {w Q a q p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hq : (Project.FirstOrderSemantics.reduct M).mem q Q)
    (hnq : ¬ (Project.FirstOrderSemantics.reduct M).mem q a)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p a) : Lt hM w p q := by
  have hn : ¬ Le hM w q p := fun h => hnq (ha.2.1 q p hp h)
  exact ⟨(le_total hM hw ((hQ p).mp (ha.1 p hp)) ((hQ q).mp hq)).resolve_right hn,hn⟩

/-- Every two actual cuts have a proper sum; no upper-bound input is retained. -/
theorem exists_sum (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) : ∃ c, Cut hM w Q c ∧ SumCut hM w Q a b c := by
  obtain ⟨q,hq,hnq⟩ := ha.2.2.2
  obtain ⟨r,hr,hnr⟩ := hb.2.2.2
  obtain ⟨aq,haq⟩ := exists_principal hM w Q q
  obtain ⟨br,hbr⟩ := exists_principal hM w Q r
  obtain ⟨s,hs⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ q).mp hq) ((hQ r).mp hr)
  obtain ⟨upper,hu⟩ := exists_principal hM w Q s
  have hsCopy := hs
  obtain ⟨i,j,k,l,n,den,_,_,hsc,_⟩ := hsCopy
  have hupper := principal_cut hM hw hQ ((hQ s).mpr ⟨n,den,hsc⟩) hu
  have hpr : ConstructionPrincipalAddition.PrincipalAdd hM w Q aq br upper := ⟨q,r,s,hq,hr,haq,hbr,hs,hu⟩
  have hbound := ConstructionBasePointBound.bound_inputs_mono
    (ConstructionBasePointBound.principal_add_bound hM hw hQ hpr)
    (fun p hp => (haq p).mpr ⟨ha.1 p hp,below_omitted hM hw hQ ha hq hnq hp⟩)
    (fun p hp => (hbr p).mpr ⟨hb.1 p hp,below_omitted hM hw hQ hb hr hnr hp⟩)
  obtain ⟨c,hc,hSum,_⟩ := ConstructionCutAddition.exists_bounded_sum hM hw hQ ha hb hupper hbound
  exact ⟨c,hc,hSum⟩

theorem sumMember_comm (hM : FirstOrder.Theory.Models M nativeZF) {w a b p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    SumMember hM w a b p ↔ SumMember hM w b a p := by
  have swap {a b p : M.Carrier .set} (h : SumMember hM w a b p) : SumMember hM w b a p := by
    rcases h with h | h | ⟨q,r,s,hq,hr,hs,hps⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨r,q,s,hr,hq,ConstructionFractionAddition.sum_comm hM hw hs,hps⟩)
  exact ⟨swap,swap⟩

theorem sum_comm (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hc : SumCut hM w Q a b c) : SumCut hM w Q b a c :=
  fun p => (hc p).trans (and_congr Iff.rfl (sumMember_comm hM hw))

theorem sum_mono {hM : FirstOrder.Theory.Models M nativeZF} {w Q a b c a' b' c' : M.Carrier .set}
    (hc : SumCut hM w Q a b c) (hc' : SumCut hM w Q a' b' c') (ha : Subset a a') (hb : Subset b b') :
    Subset c c' := by
  intro p hp
  obtain ⟨hpQ,hp⟩ := (hc p).mp hp
  refine (hc' p).mpr ⟨hpQ,?_⟩
  rcases hp with hp | hp | ⟨q,r,s,hq,hr,hs,hps⟩
  · exact Or.inl (ha p hp)
  · exact Or.inr (Or.inl (hb p hp))
  · exact Or.inr (Or.inr ⟨q,r,s,ha q hq,hb r hr,hs,hps⟩)

theorem sum_contains {hM : FirstOrder.Theory.Models M nativeZF} {w Q a b c : M.Carrier .set}
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : SumCut hM w Q a b c) : Subset a c ∧ Subset b c :=
  ⟨fun p hp => (hc p).mpr ⟨ha.1 p hp,Or.inl hp⟩,
   fun p hp => (hc p).mpr ⟨hb.1 p hp,Or.inr (Or.inl hp)⟩⟩

theorem sum_zero {hM : FirstOrder.Theory.Models M nativeZF} {w Q z a : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p z) (ha : Cut hM w Q a) :
    SumCut hM w Q z a a ∧ SumCut hM w Q a z a := by
  constructor
  · intro p
    constructor
    · exact fun hp => ⟨ha.1 p hp,Or.inr (Or.inl hp)⟩
    · rintro ⟨_,hp⟩
      rcases hp with hp | hp | ⟨q,_,_,hq,_,_,_⟩
      · exact (hz p hp).elim
      · exact hp
      · exact (hz q hq).elim
  · intro p
    constructor
    · exact fun hp => ⟨ha.1 p hp,Or.inl hp⟩
    · rintro ⟨_,hp⟩
      rcases hp with hp | hp | ⟨_,r,_,_,hr,_,_⟩
      · exact hp
      · exact (hz p hp).elim
      · exact (hz r hr).elim

def Graph (hM : FirstOrder.Theory.Models M nativeZF) (w Q R G : M.Carrier .set) : Prop := ∀ a b c,
  Product G a b c ↔ (Project.FirstOrderSemantics.reduct M).mem a R ∧
    (Project.FirstOrderSemantics.reduct M).mem b R ∧ SumCut hM w Q a b c

def Laws (R G : M.Carrier .set) : Prop :=
  (∀ a b c, Product G a b c → Product G b a c) ∧
  (∀ a b c a' b' c', Product G a b c → Product G a' b' c' → Subset a a' → Subset b b' → Subset c c') ∧
  (∀ a b c, Product G a b c → Subset a c ∧ Subset b c) ∧
  (∀ z a, (Project.FirstOrderSemantics.reduct M).mem z R → (Project.FirstOrderSemantics.reduct M).mem a R →
    (∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p z) → Product G z a a ∧ Product G a z a)

def pairSum {m : Nat} (w Q p c : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (ConstructionCutAddition.sumCut w.succ.succ Q.succ.succ 1 0 c.succ.succ)))

theorem pairSum_freeClosed {m : Nat} (w Q p c : Fin m) : (pairSum w Q p c).FreeClosed := by
  simp -implicitDefEqProofs [pairSum,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ConstructionCutAddition.sumCut_freeClosed]

theorem pairSum_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q p c : Fin m) :
    Project.Formula.satisfies env (pairSum w Q p c) ↔ ∃ a b, PureKuratowski.Code M (env.bound p) a b ∧
      SumCut hM (env.bound w) (env.bound Q) a b (env.bound c) := by
  simp only [pairSum,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,ConstructionCutAddition.sumCut_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {w Q R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) :
    ∃ I G, Representatives R R I ∧ MapsTo I R G ∧ Graph hM w Q R G ∧ Laws R G := by
  obtain ⟨I,hI⟩ := ConstructionProbeLetters.exists_representatives hM R R
  let schema : Project.BinarySchema 2 := { body := pairSum 2 3 1 0, freeClosed := pairSum_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases w (fun _ => Q), free := fun _ => w }
  have he (p c : M.Carrier .set) : schema.denote env p c ↔ ∃ a b,
      PureKuratowski.Code M p a b ∧ SumCut hM w Q a b c := pairSum_semantics hM ((env.push p).push c) 2 3 1 0
  obtain ⟨G,hG,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := I) (target := R) (by
      intro p hp
      obtain ⟨a,b,ha,hb,hp⟩ := (hI p).mp hp
      obtain ⟨c,_,hc⟩ := exists_sum hM hw hQ ((hR a).mp ha) ((hR b).mp hb)
      exact ⟨c,(he p c).mpr ⟨a,b,hp,hc⟩⟩) (by
      intro p _ c d hc hd
      obtain ⟨a,b,hp,hc⟩ := (he p c).mp hc
      obtain ⟨a',b',hp',hd⟩ := (he p d).mp hd
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact ConstructionCutAddition.sum_unique hM hc hd) (by
      intro p c hp hc
      obtain ⟨a,b,ha,hb,hp'⟩ := (hI p).mp hp
      obtain ⟨a',b',hp'',hc⟩ := (he p c).mp hc
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp' hp''
      obtain ⟨d,hd,hdSum⟩ := exists_sum hM hw hQ ((hR a).mp ha) ((hR b).mp hb)
      exact (ConstructionCutAddition.sum_unique hM hdSum hc) ▸ ((hR d).mpr hd))
  have hGraph : Graph hM w Q R G := by
    intro a b c
    constructor
    · rintro ⟨p,hp,hpc⟩
      obtain ⟨a',b',ha,hb,hp'⟩ := (hI p).mp ((hg p c).mp hpc).1
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      obtain ⟨a',b',hp',hc⟩ := (he p c).mp ((hg p c).mp hpc).2
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact ⟨ha,hb,hc⟩
    · rintro ⟨ha,hb,hc⟩
      obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM a b
      exact ⟨p,hp,(hg p c).mpr ⟨(hI p).mpr ⟨a,b,ha,hb,hp⟩,(he p c).mpr ⟨a,b,hp,hc⟩⟩⟩
  refine ⟨I,G,hI,(ForcingSupportSize.native_mapsTo hM I R G).mpr hG,hGraph,?_,?_,?_,?_⟩
  · intro a b c hc
    obtain ⟨ha,hb,hc⟩ := (hGraph a b c).mp hc
    exact (hGraph b a c).mpr ⟨hb,ha,sum_comm hM hw hc⟩
  · intro a b c a' b' c' hc hc' ha hb
    exact sum_mono ((hGraph a b c).mp hc).2.2 ((hGraph a' b' c').mp hc').2.2 ha hb
  · intro a b c hc
    obtain ⟨ha,hb,hc⟩ := (hGraph a b c).mp hc
    exact sum_contains ((hR a).mp ha) ((hR b).mp hb) hc
  · intro z a hz ha hEmpty
    obtain ⟨hl,hr⟩ := sum_zero (hM := hM) hEmpty ((hR a).mp ha)
    exact ⟨(hGraph z a a).mpr ⟨hz,ha,hl⟩,(hGraph a z a).mpr ⟨ha,hz,hr⟩⟩

/-- Literal maximum of two cuts, as used for K = max p C in the source. -/
def MaxCut (a b c : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p c ↔
    (Project.FirstOrderSemantics.reduct M).mem p a ∨ (Project.FirstOrderSemantics.reduct M).mem p b

def MaxLaws (a b c : M.Carrier .set) : Prop := Subset a c ∧ Subset b c ∧
  (∀ t, Subset a t → Subset b t → Subset c t) ∧
  (∀ t, Subset a t → ¬ Subset t a → Subset b t → ¬ Subset t b → Subset c t ∧ ¬ Subset t c)

def MaxTotal (R : M.Carrier .set) : Prop := ∀ a b,
  (Project.FirstOrderSemantics.reduct M).mem a R → (Project.FirstOrderSemantics.reduct M).mem b R →
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c R ∧ MaxCut a b c ∧ MaxLaws a b c ∧
      ∀ d, MaxCut a b d → d = c

theorem max_unique (hM : FirstOrder.Theory.Models M nativeZF) {a b c d : M.Carrier .set}
    (hc : MaxCut a b c) (hd : MaxCut a b d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => (hc p).trans (hd p).symm)

theorem exists_max (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) : ∃ c, Cut hM w Q c ∧ MaxCut a b c := by
  rcases cuts_total hM hw hQ ha hb with hab | hba
  · exact ⟨b,hb,fun p => ⟨fun hp => Or.inr hp,fun hp => hp.elim (hab p) id⟩⟩
  · exact ⟨a,ha,fun p => ⟨fun hp => Or.inl hp,fun hp => hp.elim id (hba p)⟩⟩

theorem max_cases (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : MaxCut a b c) : c = a ∨ c = b := by
  rcases cuts_total hM hw hQ ha hb with hab | hba
  · exact Or.inr (max_unique hM hc (fun p => ⟨fun hp => Or.inr hp,fun hp => hp.elim (hab p) id⟩))
  · exact Or.inl (max_unique hM hc (fun p => ⟨fun hp => Or.inl hp,fun hp => hp.elim id (hba p)⟩))

theorem max_laws (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : MaxCut a b c) : MaxLaws a b c := by
  refine ⟨fun p hp => (hc p).mpr (Or.inl hp),fun p hp => (hc p).mpr (Or.inr hp),?_,?_⟩
  · exact fun t hat hbt p hp => ((hc p).mp hp).elim (hat p) (hbt p)
  · intro t hat hta hbt htb
    rcases max_cases hM hw hQ ha hb hc with rfl | rfl
    · exact ⟨hat,hta⟩
    · exact ⟨hbt,htb⟩

theorem exists_arithmetic (hM : FirstOrder.Theory.Models M nativeZF) {w Q R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) :
    ∃ I G, Representatives R R I ∧ MapsTo I R G ∧ Graph hM w Q R G ∧ Laws R G ∧ MaxTotal R := by
  obtain ⟨I,G,hI,hG,hGraph,hLaws⟩ := exists_graph hM hw hQ hR
  refine ⟨I,G,hI,hG,hGraph,hLaws,?_⟩
  intro a b ha hb
  have hca := (hR a).mp ha
  have hcb := (hR b).mp hb
  obtain ⟨c,hc,hMax⟩ := exists_max hM hw hQ hca hcb
  exact ⟨c,(hR c).mpr hc,hMax,max_laws hM hw hQ hca hcb hMax,fun d hd => max_unique hM hd hMax⟩

end PPAC.Migration.ConstructionCutArithmetic
