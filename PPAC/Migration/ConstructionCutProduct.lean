/- Actual nonnegative cut products for the scale*height and scale*cost
operations in the pinned ProbeMargins.rawHeight/rawCost. Only native
Separation and existing function constructors are used for the sets/graphs. -/
import PPAC.Migration.ConstructionFractionProduct
import PPAC.Migration.ConstructionCutArithmetic

namespace PPAC.Migration.ConstructionCutProduct
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionProduct (product product_freeClosed product_semantics)
open ConstructionProbeLetters (Representatives)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Member (hM : FirstOrder.Theory.Models M nativeZF) (w a b p : M.Carrier .set) : Prop :=
  ∃ q r s, (Project.FirstOrderSemantics.reduct M).mem q a ∧
    (Project.FirstOrderSemantics.reduct M).mem r b ∧
    ConstructionFractionProduct.Product hM w q r s ∧ Lt hM w p s

def Value (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b c : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p c ↔
    (Project.FirstOrderSemantics.reduct M).mem p Q ∧ Member hM w a b p

def member {m : Nat} (w a b p : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound a.succ.succ.succ))
    (.conj (.mem (.bound 1) (.bound b.succ.succ.succ))
      (.conj (product w.succ.succ.succ 2 1 0) (lt w.succ.succ.succ p.succ.succ.succ 0))))))

theorem member_freeClosed {m : Nat} (w a b p : Fin m) : (member w a b p).FreeClosed := by
  simp -implicitDefEqProofs [member,Definitional.Formula.FreeClosed,product_freeClosed,lt_freeClosed]

theorem member_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w a b p : Fin m) :
    Project.Formula.satisfies env (member w a b p) ↔
      Member hM (env.bound w) (env.bound a) (env.bound b) (env.bound p) := by
  simp only [member,Member,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,product_semantics hM,lt_semantics hM]
  rfl

def value {m : Nat} (w Q a b c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound Q.succ)) (member w.succ a.succ b.succ 0)))

theorem value_freeClosed {m : Nat} (w Q a b c : Fin m) : (value w Q a b c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,member_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q a b c : Fin m) :
    Project.Formula.satisfies env (value w Q a b c) ↔
      Value hM (env.bound w) (env.bound Q) (env.bound a) (env.bound b) (env.bound c) := by
  simp only [value,Value,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,member_semantics hM]
  rfl

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF) (w Q a b : M.Carrier .set) :
    ∃ c, Value hM w Q a b c := by
  let schema : Project.UnarySchema 3 := { body := member 1 2 3 0, freeClosed := member_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases a (fun _ => b)), free := fun _ => w }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  exact ⟨c,fun p => (hc p).trans (and_congr_right (fun _ => member_semantics hM (env.push p) 1 2 3 0))⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c d : M.Carrier .set}
    (hc : Value hM w Q a b c) (hd : Value hM w Q a b d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => (hc p).trans (hd p).symm)

theorem value_cut (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value hM w Q a b c) : Cut hM w Q c := by
  refine ⟨fun p hp => ((hc p).mp hp).1,?_,?_,?_⟩
  · intro p t ht hpt
    obtain ⟨_,q,r,s,hq,hr,hs,hts⟩ := (hc t).mp ht
    have hps := le_lt_trans hM hw hpt hts
    obtain ⟨i,j,k,l,hp,_,_⟩ := hps.1
    exact (hc p).mpr ⟨(hQ p).mpr ⟨i,j,hp⟩,q,r,s,hq,hr,hs,hps⟩
  · intro p hp
    obtain ⟨_,q,r,s,hq,hr,hs,hps⟩ := (hc p).mp hp
    obtain ⟨t,ht,hpt,hts⟩ := dense hM hw hps
    exact ⟨t,(hc t).mpr ⟨(hQ t).mpr ht,q,r,s,hq,hr,hs,hts⟩,hpt⟩
  · obtain ⟨q,hq,hqa⟩ := ha.2.2.2
    obtain ⟨r,hr,hrb⟩ := hb.2.2.2
    obtain ⟨s,hs⟩ := ConstructionFractionProduct.exists_product hM hw ((hQ q).mp hq) ((hQ r).mp hr)
    refine ⟨s,(hQ s).mpr (ConstructionFractionProduct.product_range hs),?_⟩
    intro hsc
    obtain ⟨_,p,t,u,hpa,htb,hu,hsu⟩ := (hc s).mp hsc
    have hpq := ConstructionCutArithmetic.below_omitted hM hw hQ ha hq hqa hpa
    have htr := ConstructionCutArithmetic.below_omitted hM hw hQ hb hr hrb htb
    exact hsu.2 (ConstructionFractionProduct.product_mono hM hw hu hs hpq.1 htr.1)

theorem exists_product (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) : ∃ c, Cut hM w Q c ∧ Value hM w Q a b c := by
  obtain ⟨c,hc⟩ := exists_value hM w Q a b
  exact ⟨c,value_cut hM hw hQ ha hb hc,hc⟩

theorem value_comm (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hc : Value hM w Q a b c) : Value hM w Q b a c := by
  have swap {a b p : M.Carrier .set} (hp : Member hM w a b p) : Member hM w b a p := by
    obtain ⟨q,r,s,hq,hr,hs,hps⟩ := hp
    exact ⟨r,q,s,hr,hq,ConstructionFractionProduct.product_comm hM hw hs,hps⟩
  exact fun p => (hc p).trans (and_congr Iff.rfl ⟨swap,swap⟩)

theorem value_mono {hM : FirstOrder.Theory.Models M nativeZF} {w Q a b a' b' c c' : M.Carrier .set}
    (hc : Value hM w Q a b c) (hc' : Value hM w Q a' b' c') (ha : Subset a a') (hb : Subset b b') : Subset c c' := by
  intro p hp
  obtain ⟨hpQ,q,r,s,hq,hr,hs,hps⟩ := (hc p).mp hp
  exact (hc' p).mpr ⟨hpQ,q,r,s,ha q hq,hb r hr,hs,hps⟩

theorem value_zero {hM : FirstOrder.Theory.Models M nativeZF} {w Q z a : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p z) :
    Value hM w Q z a z ∧ Value hM w Q a z z := by
  constructor
  · intro p
    exact ⟨fun h => (hz p h).elim,fun ⟨_,q,_,_,hq,_,_,_⟩ => (hz q hq).elim⟩
  · intro p
    exact ⟨fun h => (hz p h).elim,fun ⟨_,_,r,_,_,hr,_,_⟩ => (hz r hr).elim⟩

/-- The product of two positive cuts is positive. The witness is obtained
inside the model using roundedness and the actual zero fraction. -/
theorem value_nonempty (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value hM w Q a b c)
    (han : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a)
    (hbn : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p b) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p c := by
  obtain ⟨p,hpa⟩ := han
  obtain ⟨q,hqa,hpq⟩ := ha.2.2.1 p hpa
  obtain ⟨r,hrb⟩ := hbn
  obtain ⟨s,hsb,hrs⟩ := hb.2.2.1 r hrb
  obtain ⟨out,hout⟩ := ConstructionFractionProduct.exists_product hM hw
    ((hQ q).mp (ha.1 q hqa)) ((hQ s).mp (hb.1 s hsb))
  have houtCopy := hout
  obtain ⟨i,j,k,l,n,den,hq,hs,ho,hn,_⟩ := houtCopy
  have hnp := ConstructionFractionAddition.mul_nonempty hM hw hq.1 hs.1
    (ConstructionFractionProduct.positive_numerator hM hw hq hpq)
    (ConstructionFractionProduct.positive_numerator hM hw hs hrs) hn
  obtain ⟨zero,hzero,hzw⟩ := hw.1.1
  obtain ⟨one,hsucc,how⟩ := hw.1.2 zero hzw
  obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM zero one
  have hzc : Coordinates w z zero one := ⟨hzw,how,⟨zero,hsucc.predecessor_mem⟩,hz⟩
  have hzo := ConstructionFractionProduct.zero_lt hM hw ho hzc hzero ⟨zero,hzero,hsucc⟩ hnp
  exact ⟨z,(hc z).mpr ⟨(hQ z).mpr ⟨zero,one,hzc⟩,q,s,out,hqa,hsb,hout,hzo⟩⟩

def Graph (hM : FirstOrder.Theory.Models M nativeZF) (w Q R G : M.Carrier .set) : Prop := ∀ a b c,
  ForcingDiagramOrder.Product G a b c ↔ (Project.FirstOrderSemantics.reduct M).mem a R ∧
    (Project.FirstOrderSemantics.reduct M).mem b R ∧ Value hM w Q a b c

def Laws (R G : M.Carrier .set) : Prop :=
  (∀ a b c, ForcingDiagramOrder.Product G a b c → ForcingDiagramOrder.Product G b a c) ∧
  (∀ a b c a' b' c', ForcingDiagramOrder.Product G a b c → ForcingDiagramOrder.Product G a' b' c' →
    Subset a a' → Subset b b' → Subset c c') ∧
  (∀ z a, (Project.FirstOrderSemantics.reduct M).mem z R → (Project.FirstOrderSemantics.reduct M).mem a R →
    (∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p z) →
    ForcingDiagramOrder.Product G z a z ∧ ForcingDiagramOrder.Product G a z z) ∧
  (∀ a b c, ForcingDiagramOrder.Product G a b c →
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) →
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p b) →
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p c)

def pairValue {m : Nat} (w Q p c : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (value w.succ.succ Q.succ.succ 1 0 c.succ.succ)))

theorem pairValue_freeClosed {m : Nat} (w Q p c : Fin m) : (pairValue w Q p c).FreeClosed := by
  simp -implicitDefEqProofs [pairValue,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,value_freeClosed]

theorem pairValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q p c : Fin m) :
    Project.Formula.satisfies env (pairValue w Q p c) ↔ ∃ a b, PureKuratowski.Code M (env.bound p) a b ∧
      Value hM (env.bound w) (env.bound Q) a b (env.bound c) := by
  simp only [pairValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,value_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {w Q R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) :
    ∃ I G, Representatives R R I ∧ MapsTo I R G ∧ Graph hM w Q R G := by
  obtain ⟨I,hI⟩ := ConstructionProbeLetters.exists_representatives hM R R
  let schema : Project.BinarySchema 2 := { body := pairValue 2 3 1 0, freeClosed := pairValue_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases w (fun _ => Q), free := fun _ => w }
  have he (p c : M.Carrier .set) : schema.denote env p c ↔ ∃ a b,
      PureKuratowski.Code M p a b ∧ Value hM w Q a b c := pairValue_semantics hM ((env.push p).push c) 2 3 1 0
  obtain ⟨G,hG,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := I) (target := R) (by
      intro p hp
      obtain ⟨a,b,ha,hb,hp⟩ := (hI p).mp hp
      obtain ⟨c,_,hc⟩ := exists_product hM hw hQ ((hR a).mp ha) ((hR b).mp hb)
      exact ⟨c,(he p c).mpr ⟨a,b,hp,hc⟩⟩) (by
      intro p _ c d hc hd
      obtain ⟨a,b,hp,hc⟩ := (he p c).mp hc
      obtain ⟨a',b',hp',hd⟩ := (he p d).mp hd
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact value_unique hM hc hd) (by
      intro p c hp hc
      obtain ⟨a,b,ha,hb,hp'⟩ := (hI p).mp hp
      obtain ⟨a',b',hp'',hc⟩ := (he p c).mp hc
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp' hp''
      exact (hR c).mpr (value_cut hM hw hQ ((hR a).mp ha) ((hR b).mp hb) hc))
  refine ⟨I,G,hI,(ForcingSupportSize.native_mapsTo hM I R G).mpr hG,?_⟩
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

theorem graph_laws (hM : FirstOrder.Theory.Models M nativeZF) {w Q R G : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hR : CutCarrier hM w Q R) (hg : Graph hM w Q R G) : Laws R G := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b c hc
    obtain ⟨ha,hb,hc⟩ := (hg a b c).mp hc
    exact (hg b a c).mpr ⟨hb,ha,value_comm hM hw hc⟩
  · intro a b c a' b' c' hc hc' ha hb
    exact value_mono ((hg a b c).mp hc).2.2 ((hg a' b' c').mp hc').2.2 ha hb
  · intro z a hz ha hEmpty
    obtain ⟨hl,hr⟩ := value_zero (hM := hM) (w := w) (Q := Q) (a := a) hEmpty
    exact ⟨(hg z a z).mpr ⟨hz,ha,hl⟩,(hg a z z).mpr ⟨ha,hz,hr⟩⟩
  · intro a b c hc
    obtain ⟨ha,hb,hc⟩ := (hg a b c).mp hc
    exact value_nonempty hM hw hQ ((hR a).mp ha) ((hR b).mp hb) hc

end PPAC.Migration.ConstructionCutProduct
