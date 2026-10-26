/- Internal rational addition for pinned Base.margin / HeightCost arithmetic.
All natural arithmetic is reused from the native library. Equivalent rational
representations remain codes; order/equivalence compatibility is proved below. -/
import PPAC.Migration.ConstructionRealCuts

namespace PPAC.Migration.ConstructionFractionAddition
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem add_range (hM : FirstOrder.Theory.Models M nativeZF) {w a b s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hs : Add hM a b s) : (Project.FirstOrderSemantics.reduct M).mem s w :=
  ZF.ordinalAddition_mem_omega (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hw ha hb hs

theorem add_le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w a x y ax ay : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hx : (Project.FirstOrderSemantics.reduct M).mem x w)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w) (hax : Add hM a x ax) (hay : Add hM a y ay) :
    NatLe ax ay ↔ NatLe x y := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have inc := ZF.ordinalAddition_isIncreasingOnOrdinals hZF (KuratowskiZF.interpretation hM) (ord a ha)
  constructor
  · intro h
    rcases nat_compare hM hw hx hy with he | hxy | hyx
    · exact Or.inl he
    · exact Or.inr hxy
    · exact (nat_not_reverse hM hw (add_range hM hw ha hy hay) h
        (inc y x (ord y hy) (ord x hx) hyx ay ax hay hax)).elim
  · rintro (he | hxy)
    · subst y
      exact Or.inl (ConstructionBaseMonoid.addition_unique hM hw hx hax hay)
    · exact Or.inr (inc x y (ord x hx) (ord y hy) hxy ax ay hax hay)

theorem mul_nonempty (hM : FirstOrder.Theory.Models M nativeZF) {w a b p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (han : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z a) (hbn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z b)
    (hp : Mul hM a b p) : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  rcases ZF.ordinalMultiplication_right_eq_or_mem hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF a ha) han (hw.members_areOrdinals hZF b hb) hp with he | hbp
  · exact he ▸ hbn
  · exact ⟨b,hbp⟩

def Data (hM : FirstOrder.Theory.Models M nativeZF) (a b c d n den : M.Carrier .set) : Prop :=
  ∃ ad cb, Mul hM a d ad ∧ Mul hM c b cb ∧ Add hM ad cb n ∧ Mul hM b d den

def Sum (hM : FirstOrder.Theory.Models M nativeZF) (w q r s : M.Carrier .set) : Prop :=
  ∃ a b c d n den, Coordinates w q a b ∧ Coordinates w r c d ∧
    Coordinates w s n den ∧ Data hM a b c d n den

theorem sum_exists (hM : FirstOrder.Theory.Models M nativeZF) {w q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Fraction w q) (hr : Fraction w r) :
    ∃ s, Sum hM w q r s := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨c,d,hr⟩ := hr
  obtain ⟨ad,hAd,had⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨cb,hCb,hcb⟩ := mul_exists hM hw hr.1 hq.2.1
  obtain ⟨n,hn,hadd⟩ := add_exists hM hw hAd hCb
  obtain ⟨den,hden,hmul⟩ := mul_exists hM hw hq.2.1 hr.2.1
  obtain ⟨s,hs⟩ := KuratowskiZF.exists_code hM n den
  exact ⟨s,a,b,c,d,n,den,hq,hr,⟨hn,hden,mul_nonempty hM hw hq.2.1 hr.2.1 hq.2.2.1 hr.2.2.1 hmul,hs⟩,
    ad,cb,had,hcb,hadd,hmul⟩

theorem sum_unique (hM : FirstOrder.Theory.Models M nativeZF) {w q r s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hs : Sum hM w q r s) (ht : Sum hM w q r t) : s = t := by
  obtain ⟨a,b,c,d,n,den,hq,hr,hs,ad,cb,had,hcb,hadd,hmul⟩ := hs
  obtain ⟨a',b',c',d',n',den',hq',hr',ht,ad',cb',had',hcb',hadd',hmul'⟩ := ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq.2.2.2 hq'.2.2.2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
  have ead := mul_unique hM hw hr.2.1 had had'
  have ecb := mul_unique hM hw hq.2.1 hcb hcb'
  have eden := mul_unique hM hw hr.2.1 hmul hmul'
  subst ad'; subst cb'; subst den'
  have en := ConstructionBaseMonoid.addition_unique hM hw (mul_range hM hw hr.1 hq.2.1 hcb) hadd hadd'
  subst n'
  exact KuratowskiZF.code_unique hM hs.2.2.2 ht.2.2.2

theorem sum_comm (hM : FirstOrder.Theory.Models M nativeZF) {w q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hs : Sum hM w q r s) : Sum hM w r q s := by
  obtain ⟨a,b,c,d,n,den,hq,hr,hs,ad,cb,had,hcb,hadd,hmul⟩ := hs
  exact ⟨c,d,a,b,n,den,hr,hq,hs,cb,ad,hcb,had,
    add_comm hM hw (mul_range hM hw hq.1 hr.2.1 had) (mul_range hM hw hr.1 hq.2.1 hcb) hadd,
    mul_comm hM hw hq.2.1 hr.2.1 hmul⟩

/-- Addition by a fixed fraction reflects as well as preserves order. -/
theorem sum_right_le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w q r t s u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hsum : Sum hM w q t s) (hadd : Sum hM w r t u) : Le hM w s u ↔ Le hM w q r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨a,b,e,f,n,bf,hq,ht,hs,af,eb,haf,heb,hn,hbf⟩ := hsum
  obtain ⟨c,d,e',f',m,df,hr,ht',hu,cf,ed,hcf,hed,hm,hdf⟩ := hadd
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht.2.2.2 ht'.2.2.2
  have hAf := mul_range hM hw hq.1 ht.2.1 haf
  have hEb := mul_range hM hw ht.1 hq.2.1 heb
  have hCf := mul_range hM hw hr.1 ht.2.1 hcf
  have hEd := mul_range hM hw ht.1 hr.2.1 hed
  obtain ⟨nd,hNd,hnd⟩ := mul_exists hM hw hs.1 hr.2.1
  obtain ⟨mb,hMb,hmb⟩ := mul_exists hM hw hu.1 hq.2.1
  obtain ⟨ndf,_,hndf⟩ := mul_exists hM hw hNd ht.2.1
  obtain ⟨mbf,_,hmbf⟩ := mul_exists hM hw hMb ht.2.1
  obtain ⟨n_df,_,hn_df⟩ := mul_exists hM hw hs.1 hu.2.1
  obtain ⟨m_bf,_,hm_bf⟩ := mul_exists hM hw hu.1 hs.2.1
  have en := ZF.ordinalMultiplication_assoc hZF I (ord n hs.1) (ord d hr.2.1) (ord f ht.2.1) hnd hdf hn_df hndf
  have em := ZF.ordinalMultiplication_assoc hZF I (ord m hu.1) (ord b hq.2.1) (ord f ht.2.1) hmb hbf hm_bf hmbf
  have first : Le hM w s u ↔ NatLe nd mb := by
    rw [le_iff_products hM hw hs hu hn_df hm_bf,en,em]
    exact mul_le_iff hM hw ht.2.1 ht.2.2.1 hNd hMb
      (mul_comm hM hw hNd ht.2.1 hndf) (mul_comm hM hw hMb ht.2.1 hmbf)
  obtain ⟨ad,hAd,had⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨cb,hCb,hcb⟩ := mul_exists hM hw hr.1 hq.2.1
  obtain ⟨adf,hAdf,hadf⟩ := mul_exists hM hw hAd ht.2.1
  obtain ⟨cbf,hCbf,hcbf⟩ := mul_exists hM hw hCb ht.2.1
  obtain ⟨afd,hAfd,hafd⟩ := mul_exists hM hw hAf hr.2.1
  obtain ⟨cfb,hCfb,hcfb⟩ := mul_exists hM hw hCf hq.2.1
  obtain ⟨ebd,hEbd,hebd⟩ := mul_exists hM hw hEb hr.2.1
  obtain ⟨edb,hEdb,hedb⟩ := mul_exists hM hw hEd hq.2.1
  have ea := mul_swap hM hw hq.1 ht.2.1 hr.2.1 haf had hafd hadf
  have ec := mul_swap hM hw hr.1 ht.2.1 hq.2.1 hcf hcb hcfb hcbf
  have ee := mul_swap hM hw ht.1 hq.2.1 hr.2.1 heb hed hebd hedb
  have hnd_add := mul_add hM hw hr.2.1 hAf hEb hn (mul_comm hM hw hs.1 hr.2.1 hnd)
    (mul_comm hM hw hAf hr.2.1 hafd) (mul_comm hM hw hEb hr.2.1 hebd)
  have hmb_add := mul_add hM hw hq.2.1 hCf hEd hm (mul_comm hM hw hu.1 hq.2.1 hmb)
    (mul_comm hM hw hCf hq.2.1 hcfb) (mul_comm hM hw hEd hq.2.1 hedb)
  have second : NatLe nd mb ↔ NatLe adf cbf := by
    have hl : Add hM ebd adf nd := ea ▸ add_comm hM hw hAfd hEbd hnd_add
    have hr' : Add hM ebd cbf mb := ee.symm ▸ ec ▸ add_comm hM hw hCfb hEdb hmb_add
    exact add_le_iff hM hw hEbd hAdf hCbf hl hr'
  have third : NatLe adf cbf ↔ NatLe ad cb :=
    mul_le_iff hM hw ht.2.1 ht.2.2.1 hAd hCb (mul_comm hM hw hAd ht.2.1 hadf) (mul_comm hM hw hCb ht.2.1 hcbf)
  exact first.trans (second.trans (third.trans (le_iff_products hM hw hq hr had hcb).symm))

theorem sum_left_le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w q r t s u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Sum hM w t q s) (hu : Sum hM w t r u) : Le hM w s u ↔ Le hM w q r :=
  sum_right_le_iff hM hw (sum_comm hM hw hs) (sum_comm hM hw hu)

theorem sum_right_lt_iff (hM : FirstOrder.Theory.Models M nativeZF) {w q r t s u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Sum hM w q t s) (hu : Sum hM w r t u) : Lt hM w s u ↔ Lt hM w q r := by
  exact and_congr (sum_right_le_iff hM hw hs hu) (not_congr (sum_right_le_iff hM hw hu hs))

theorem sum_mono (hM : FirstOrder.Theory.Models M nativeZF) {w q q' r r' s s' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Sum hM w q r s) (hs' : Sum hM w q' r' s') (hq : Le hM w q q') (hr : Le hM w r r') : Le hM w s s' := by
  have hsCopy := hs
  have hsCopy' := hs'
  obtain ⟨a,b,c,d,n,den,hqC,_,_⟩ := hsCopy
  obtain ⟨a',b',c',d',n',den',_,hrC,_⟩ := hsCopy'
  obtain ⟨middle,hm⟩ := sum_exists hM hw ⟨a,b,hqC⟩ ⟨c',d',hrC⟩
  exact le_trans hM hw ((sum_left_le_iff hM hw hs hm).mpr hr) ((sum_right_le_iff hM hw hm hs').mpr hq)

/-- Changing representatives changes the output code only within its value class. -/
theorem sum_equiv (hM : FirstOrder.Theory.Models M nativeZF) {w q q' r r' s s' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Sum hM w q r s) (hs' : Sum hM w q' r' s')
    (hq : Le hM w q q' ∧ Le hM w q' q) (hr : Le hM w r r' ∧ Le hM w r' r) :
    Le hM w s s' ∧ Le hM w s' s :=
  ⟨sum_mono hM hw hs hs' hq.1 hr.1,sum_mono hM hw hs' hs hq.2 hr.2⟩

theorem principal_sum_independent (hM : FirstOrder.Theory.Models M nativeZF) {w Q q q' r r' s s' c c' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hs : Sum hM w q r s) (hs' : Sum hM w q' r' s')
    (hq : Le hM w q q' ∧ Le hM w q' q) (hr : Le hM w r r' ∧ Le hM w r' r)
    (hc : ConstructionRealCuts.Principal hM w Q s c) (hc' : ConstructionRealCuts.Principal hM w Q s' c') : c = c' := by
  have he := sum_equiv hM hw hs hs' hq hr
  obtain ⟨a,b,d,e,hsc,hs'c,_⟩ := he.1
  exact (ConstructionRealCuts.principal_eq_iff hM hw hQ ((hQ s).mpr ⟨a,b,hsc⟩)
    ((hQ s').mpr ⟨d,e,hs'c⟩) hc hc').mpr he

def dataF {m : Nat} (a b c d n den : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj
    (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention (.bound 1) (.bound a.succ.succ) (.bound d.succ.succ))
    (.conj (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention (.bound 0) (.bound c.succ.succ) (.bound b.succ.succ))
      (.conj (Project.Formula.isOrdinalAddition PureKuratowskiProject.convention (.bound n.succ.succ) (.bound 1) (.bound 0))
        (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention (.bound den.succ.succ) (.bound b.succ.succ) (.bound d.succ.succ))))))

theorem dataF_freeClosed {m : Nat} (a b c d n den : Fin m) : (dataF a b c d n den).FreeClosed := by
  simp -implicitDefEqProofs [dataF,Definitional.Formula.FreeClosed]

theorem dataF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (a b c d n den : Fin m) :
    Project.Formula.satisfies env (dataF a b c d n den) ↔
      Data hM (env.bound a) (env.bound b) (env.bound c) (env.bound d) (env.bound n) (env.bound den) := by
  simp only [dataF,Data,ConstructionFractionOrder.Mul,ConstructionFractionDensity.Add,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOrdinalMultiplication_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isOrdinalAddition_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def sum {m : Nat} (w q r s : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (coordinates w.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ 5 4)
      (.conj (coordinates w.succ.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ.succ 3 2)
        (.conj (coordinates w.succ.succ.succ.succ.succ.succ s.succ.succ.succ.succ.succ.succ 1 0)
          (dataF (5 : Fin (m+6)) 4 3 2 1 0)))))))))

theorem sum_freeClosed {m : Nat} (w q r s : Fin m) : (sum w q r s).FreeClosed := by
  simp -implicitDefEqProofs [sum,Definitional.Formula.FreeClosed,coordinates_freeClosed,dataF_freeClosed]

theorem sum_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q r s : Fin m) :
    Project.Formula.satisfies env (sum w q r s) ↔ Sum hM (env.bound w) (env.bound q) (env.bound r) (env.bound s) := by
  simp only [sum,Sum,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,coordinates_semantics hM,dataF_semantics hM]
  rfl

def totalUnique {m : Nat} (w : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (fraction w.succ.succ 1) (.imp (fraction w.succ.succ 0)
    (.existsE (.conj (sum w.succ.succ.succ 2 1 0) (.forallE (.imp
      (sum w.succ.succ.succ.succ 3 2 0) (Project.Formula.extensionalEq (.bound 0) (.bound 1)))))))))

theorem totalUnique_freeClosed {m : Nat} (w : Fin m) : (totalUnique w).FreeClosed := by
  simp -implicitDefEqProofs [totalUnique,Definitional.Formula.FreeClosed,fraction_freeClosed,sum_freeClosed]

theorem totalUnique_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w : Fin m) :
    Project.Formula.satisfies env (totalUnique w) ↔ ∀ q r, Fraction (env.bound w) q → Fraction (env.bound w) r →
      ∃ s, Sum hM (env.bound w) q r s ∧ ∀ t, Sum hM (env.bound w) q r t → t = s := by
  simp only [totalUnique,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,fraction_semantics hM,sum_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def commutative {m : Nat} (w : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (sum w.succ.succ.succ 2 1 0) (sum w.succ.succ.succ 1 2 0))))

theorem commutative_freeClosed {m : Nat} (w : Fin m) : (commutative w).FreeClosed := by
  simp -implicitDefEqProofs [commutative,Definitional.Formula.FreeClosed,sum_freeClosed]

theorem commutative_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w : Fin m) :
    Project.Formula.satisfies env (commutative w) ↔ ∀ q r s, Sum hM (env.bound w) q r s → Sum hM (env.bound w) r q s := by
  simp only [commutative,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,sum_semantics hM]
  rfl

def orderReflection {m : Nat} (w : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (sum w.succ.succ.succ.succ.succ 4 2 1) (.imp (sum w.succ.succ.succ.succ.succ 3 2 0)
      (.conj (.iff (le w.succ.succ.succ.succ.succ 1 0) (le w.succ.succ.succ.succ.succ 4 3))
        (.iff (lt w.succ.succ.succ.succ.succ 1 0) (lt w.succ.succ.succ.succ.succ 4 3)))))))))

theorem orderReflection_freeClosed {m : Nat} (w : Fin m) : (orderReflection w).FreeClosed := by
  simp -implicitDefEqProofs [orderReflection,Definitional.Formula.FreeClosed,sum_freeClosed,le_freeClosed,lt_freeClosed]

theorem orderReflection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w : Fin m) :
    Project.Formula.satisfies env (orderReflection w) ↔ ∀ q r t s v,
      Sum hM (env.bound w) q t s → Sum hM (env.bound w) r t v →
        (Le hM (env.bound w) s v ↔ Le hM (env.bound w) q r) ∧
        (Lt hM (env.bound w) s v ↔ Lt hM (env.bound w) q r) := by
  simp only [orderReflection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,sum_semantics hM,le_semantics hM,lt_semantics hM]
  rfl

def additionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.conj (totalUnique (0 : Fin 1)) (.conj (commutative (0 : Fin 1)) (orderReflection (0 : Fin 1)))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,totalUnique_freeClosed,commutative_freeClosed,orderReflection_freeClosed]

theorem addition_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence additionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) additionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_conj_iff,totalUnique_semantics hM,commutative_semantics hM,orderReflection_semantics hM]
  intro hw
  refine ⟨?_,fun _ _ _ hs => sum_comm hM hw hs,fun _ _ _ _ _ hs hu =>
    ⟨sum_right_le_iff hM hw hs hu,sum_right_lt_iff hM hw hs hu⟩⟩
  intro q r hq hr
  obtain ⟨s,hs⟩ := sum_exists hM hw hq hr
  exact ⟨s,hs,fun _ ht => sum_unique hM hw ht hs⟩

theorem addition_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence additionSentence) := ModelTransfer.derives (fun _ hM => addition_models hM)

end PPAC.Migration.ConstructionFractionAddition
