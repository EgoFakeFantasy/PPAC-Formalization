/- Ordered fraction input for the internal interpretation of source Base
height/cost. All arithmetic is the existing native arithmetic on internal
omega. Pair codes form a total preorder, not an antisymmetric order: equal
fractions may have distinct codes. No real-field completion is asserted. -/
import PPAC.Migration.ConstructionBaseWeights
import YesMetaZFC.SetTheory.Ord.NaturalPrime

namespace PPAC.Migration.ConstructionFractionOrder
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

abbrev Mul (hM : FirstOrder.Theory.Models M nativeZF) (a b p : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOrdinalMultiplication (KuratowskiZF.interpretation hM) p a b

def NatLe (x y : M.Carrier .set) : Prop := x = y ∨ (Project.FirstOrderSemantics.reduct M).mem x y

theorem nat_compare (hM : FirstOrder.Theory.Models M nativeZF) {w x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x w) (hy : (Project.FirstOrderSemantics.reduct M).mem y w) :
    x = y ∨ (Project.FirstOrderSemantics.reduct M).mem x y ∨ (Project.FirstOrderSemantics.reduct M).mem y x := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  rcases (hw.isOrdinal hZF).wellOrder.linear.compare x hx y hy with he | hxy | hyx
  · exact Or.inl (hZF.1.eq_of_same_members x y he)
  · exact Or.inr (Or.inl hxy)
  · exact Or.inr (Or.inr hyx)

theorem nat_not_reverse (hM : FirstOrder.Theory.Models M nativeZF) {w x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w) (hle : NatLe x y)
    (hlt : (Project.FirstOrderSemantics.reduct M).mem y x) : False := by
  have ho := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) y hy
  have hyy : (Project.FirstOrderSemantics.reduct M).mem y y := by
    rcases hle with he | hxy
    · exact he ▸ hlt
    · exact ho.transitive x hxy y hlt
  exact KP.mem_irrefl_d (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) y hyy

theorem mul_exists (hM : FirstOrder.Theory.Models M nativeZF) {w a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p w ∧ Mul hM a b p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨p,hp,_⟩ := ZF.ordinalMultiplication_existsUnique hZF (KuratowskiZF.interpretation hM) a
    (hw.members_areOrdinals hZF b hb)
  exact ⟨p,ZF.ordinalMultiplication_mem_omega hZF (KuratowskiZF.interpretation hM) hw ha hb hp,hp⟩

theorem mul_range (hM : FirstOrder.Theory.Models M nativeZF) {w a b p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hp : Mul hM a b p) : (Project.FirstOrderSemantics.reduct M).mem p w :=
  ZF.ordinalMultiplication_mem_omega (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hw ha hb hp

theorem mul_unique (hM : FirstOrder.Theory.Models M nativeZF) {w a b p q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hp : Mul hM a b p) (hq : Mul hM a b q) : p = q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨r,_,hr⟩ := ZF.ordinalMultiplication_existsUnique hZF (KuratowskiZF.interpretation hM) a
    (hw.members_areOrdinals hZF b hb)
  exact (hr p hp).trans (hr q hq).symm

/-- Direct reuse of the native internal-natural commutativity theorem. -/
theorem mul_comm (hM : FirstOrder.Theory.Models M nativeZF) {w a b p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hp : Mul hM a b p) : Mul hM b a p := by
  obtain ⟨q,_,hq⟩ := mul_exists hM hw hb ha
  have he := SetTheory.Structure.natural_mul_comm (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hw ha hb hp hq
  exact he.symm ▸ hq

theorem mul_le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w a x y ax ay : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w)
    (han : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z a)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x w) (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (hax : Mul hM a x ax) (hay : Mul hM a y ay) : NatLe ax ay ↔ NatLe x y := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have inc := ZF.ordinalMultiplication_isIncreasingOnOrdinals hZF (KuratowskiZF.interpretation hM) (ord a ha) han
  constructor
  · intro h
    rcases nat_compare hM hw hx hy with he | hxy | hyx
    · exact Or.inl he
    · exact Or.inr hxy
    · exact (nat_not_reverse hM hw (mul_range hM hw ha hy hay) h
        (inc y x (ord y hy) (ord x hx) hyx ay ax hay hax)).elim
  · rintro (he | hxy)
    · subst y
      exact Or.inl (mul_unique hM hw hx hax hay)
    · exact Or.inr (inc x y (ord x hx) (ord y hy) hxy ax ay hax hay)

/-- a*b*c = a*c*b, retaining every internal intermediate product witness. -/
theorem mul_swap (hM : FirstOrder.Theory.Models M nativeZF) {w a b c ab ac abc acb : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c w)
    (hab : Mul hM a b ab) (hac : Mul hM a c ac) (habc : Mul hM ab c abc) (hacb : Mul hM ac b acb) : abc = acb := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨bc,hbcw,hbc⟩ := mul_exists hM hw hb hc
  obtain ⟨r,_,hr⟩ := mul_exists hM hw ha hbcw
  have he1 := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord a ha) (ord b hb) (ord c hc) hab hbc hr habc
  have he2 := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord a ha) (ord c hc) (ord b hb) hac (mul_comm hM hw hb hc hbc) hr hacb
  exact he1.symm.trans he2

def Coordinates (w q a b : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem a w ∧ (Project.FirstOrderSemantics.reduct M).mem b w ∧
  (∃ z, (Project.FirstOrderSemantics.reduct M).mem z b) ∧ PureKuratowski.Code M q a b

def Fraction (w q : M.Carrier .set) : Prop := ∃ a b, Coordinates w q a b

def Cross (hM : FirstOrder.Theory.Models M nativeZF) (a b c d : M.Carrier .set) : Prop :=
  ∃ u v, Mul hM a d u ∧ Mul hM c b v ∧ NatLe u v

def Le (hM : FirstOrder.Theory.Models M nativeZF) (w q r : M.Carrier .set) : Prop :=
  ∃ a b c d, Coordinates w q a b ∧ Coordinates w r c d ∧ Cross hM a b c d

theorem le_iff_cross (hM : FirstOrder.Theory.Models M nativeZF) {w q r a b c d : M.Carrier .set}
    (hq : Coordinates w q a b) (hr : Coordinates w r c d) : Le hM w q r ↔ Cross hM a b c d := by
  constructor
  · rintro ⟨a',b',c',d',hq',hr',h⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq.2.2.2 hq'.2.2.2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
    exact h
  · exact fun h => ⟨a,b,c,d,hq,hr,h⟩

theorem le_refl (hM : FirstOrder.Theory.Models M nativeZF) {w q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Fraction w q) : Le hM w q q := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨ab,_,hab⟩ := mul_exists hM hw hq.1 hq.2.1
  exact (le_iff_cross hM hq hq).mpr ⟨ab,ab,hab,hab,Or.inl rfl⟩

theorem le_total (hM : FirstOrder.Theory.Models M nativeZF) {w q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Fraction w q) (hr : Fraction w r) :
    Le hM w q r ∨ Le hM w r q := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨c,d,hr⟩ := hr
  obtain ⟨ad,hadw,had⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨cb,hcbw,hcb⟩ := mul_exists hM hw hr.1 hq.2.1
  rcases nat_compare hM hw hadw hcbw with he | hlt | hgt
  · exact Or.inl ((le_iff_cross hM hq hr).mpr ⟨ad,cb,had,hcb,Or.inl he⟩)
  · exact Or.inl ((le_iff_cross hM hq hr).mpr ⟨ad,cb,had,hcb,Or.inr hlt⟩)
  · exact Or.inr ((le_iff_cross hM hr hq).mpr ⟨cb,ad,hcb,had,Or.inr hgt⟩)

theorem le_trans (hM : FirstOrder.Theory.Models M nativeZF) {w q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hqr : Le hM w q r) (hrs : Le hM w r s) : Le hM w q s := by
  obtain ⟨a,b,c,d,hq,hr,ad,cb,had,hcb,h1⟩ := hqr
  obtain ⟨c',d',e,f,hr',hs,cf,ed,hcf,hed,h2⟩ := hrs
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
  have hAd := mul_range hM hw hq.1 hr.2.1 had
  have hCb := mul_range hM hw hr.1 hq.2.1 hcb
  have hCf := mul_range hM hw hr.1 hs.2.1 hcf
  have hEd := mul_range hM hw hs.1 hr.2.1 hed
  obtain ⟨fad,_,hfad⟩ := mul_exists hM hw hs.2.1 hAd
  obtain ⟨fcb,hFcb,hfcb⟩ := mul_exists hM hw hs.2.1 hCb
  obtain ⟨bcf,_,hbcf⟩ := mul_exists hM hw hq.2.1 hCf
  obtain ⟨bed,hBed,hbed⟩ := mul_exists hM hw hq.2.1 hEd
  have h1' := (mul_le_iff hM hw hs.2.1 hs.2.2.1 hAd hCb hfad hfcb).mpr h1
  have h2' := (mul_le_iff hM hw hq.2.1 hq.2.2.1 hCf hEd hbcf hbed).mpr h2
  have hm := mul_swap hM hw hr.1 hq.2.1 hs.2.1 hcb hcf
    (mul_comm hM hw hs.2.1 hCb hfcb) (mul_comm hM hw hq.2.1 hCf hbcf)
  have h3 : NatLe fad bed := ZF.eqOrMem_trans
    (hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) bed hBed) h1' (hm.symm ▸ h2')
  obtain ⟨af,hAf,haf⟩ := mul_exists hM hw hq.1 hs.2.1
  obtain ⟨eb,hEb,heb⟩ := mul_exists hM hw hs.1 hq.2.1
  obtain ⟨daf,_,hdaf⟩ := mul_exists hM hw hr.2.1 hAf
  obtain ⟨deb,_,hdeb⟩ := mul_exists hM hw hr.2.1 hEb
  have hl := mul_swap hM hw hq.1 hr.2.1 hs.2.1 had haf
    (mul_comm hM hw hs.2.1 hAd hfad) (mul_comm hM hw hr.2.1 hAf hdaf)
  have hr' := mul_swap hM hw hs.1 hr.2.1 hq.2.1 hed heb
    (mul_comm hM hw hq.2.1 hEd hbed) (mul_comm hM hw hr.2.1 hEb hdeb)
  have h4 : NatLe daf deb := hl ▸ hr' ▸ h3
  exact (le_iff_cross hM hq hs).mpr ⟨af,eb,haf,heb,
    (mul_le_iff hM hw hr.2.1 hr.2.2.1 hAf hEb hdaf hdeb).mp h4⟩

def coordinates {m : Nat} (w q a b : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound a) (.bound w)) (.conj (.mem (.bound b) (.bound w))
    (.conj (.existsE (.mem (.bound 0) (.bound b.succ)))
      (PureKuratowskiProject.code (.bound q) (.bound a) (.bound b))))

theorem coordinates_freeClosed {m : Nat} (w q a b : Fin m) : (coordinates w q a b).FreeClosed := by
  simp -implicitDefEqProofs [coordinates,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem coordinates_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q a b : Fin m) :
    Project.Formula.satisfies env (coordinates w q a b) ↔
      Coordinates (env.bound w) (env.bound q) (env.bound a) (env.bound b) := by
  simp only [coordinates,Coordinates,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff,KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

def fraction {m : Nat} (w q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (coordinates w.succ.succ q.succ.succ 1 0))

theorem fraction_freeClosed {m : Nat} (w q : Fin m) : (fraction w q).FreeClosed := by
  simp -implicitDefEqProofs [fraction,Definitional.Formula.FreeClosed,coordinates_freeClosed]

theorem fraction_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q : Fin m) :
    Project.Formula.satisfies env (fraction w q) ↔ Fraction (env.bound w) (env.bound q) := by
  simp only [fraction,Fraction,Project.Formula.satisfies_exists_iff,coordinates_semantics hM]
  rfl

def cross {m : Nat} (a b c d : Fin m) : Project.Formula 1 m := .existsE (.existsE
  (.conj (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention
    (.bound 1) (.bound a.succ.succ) (.bound d.succ.succ))
    (.conj (Project.Formula.isOrdinalMultiplication PureKuratowskiProject.convention
      (.bound 0) (.bound c.succ.succ) (.bound b.succ.succ))
      (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))))))

theorem cross_freeClosed {m : Nat} (a b c d : Fin m) : (cross a b c d).FreeClosed := by
  simp -implicitDefEqProofs [cross,Definitional.Formula.FreeClosed]

theorem cross_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (a b c d : Fin m) :
    Project.Formula.satisfies env (cross a b c d) ↔ Cross hM (env.bound a) (env.bound b) (env.bound c) (env.bound d) := by
  simp only [cross,Cross,Mul,NatLe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOrdinalMultiplication_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def le {m : Nat} (w q r : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (coordinates w.succ.succ.succ.succ q.succ.succ.succ.succ 3 2)
      (.conj (coordinates w.succ.succ.succ.succ r.succ.succ.succ.succ 1 0) (cross (3 : Fin (m+4)) 2 1 0))))))

theorem le_freeClosed {m : Nat} (w q r : Fin m) : (le w q r).FreeClosed := by
  simp -implicitDefEqProofs [le,Definitional.Formula.FreeClosed,coordinates_freeClosed,cross_freeClosed]

theorem le_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w q r : Fin m) :
    Project.Formula.satisfies env (le w q r) ↔ Le hM (env.bound w) (env.bound q) (env.bound r) := by
  simp only [le,Le,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coordinates_semantics hM,cross_semantics hM]
  rfl

def Carrier (w Q : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q Q ↔ Fraction w q

def carrier {m : Nat} (w Q : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound Q.succ)) (fraction w.succ 0))

theorem carrier_freeClosed {m : Nat} (w Q : Fin m) : (carrier w Q).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,fraction_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q : Fin m) :
    Project.Formula.satisfies env (carrier w Q) ↔ Carrier (env.bound w) (env.bound Q) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,fraction_semantics hM,Project.Term.eval_bound]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (w : M.Carrier .set) : ∃ Q, Carrier w Q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨pairs,hpairs⟩ := ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) w w
  let schema : Project.UnarySchema 1 := { body := fraction 1 0, freeClosed := fraction_freeClosed _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => w, free := fun _ => w }
  obtain ⟨Q,hQ⟩ := ZF.separation_exists_d hZF schema env pairs
  have he : ∀ q, Project.Formula.satisfies (env.push q) schema.body ↔ Fraction w q :=
    fun q => fraction_semantics hM (env.push q) 1 0
  refine ⟨Q,fun q => ?_⟩
  constructor
  · exact fun h => (he q).mp ((hQ q).mp h).2
  · intro hq
    obtain ⟨a,b,ha,hb,hbn,hc⟩ := hq
    exact (hQ q).mpr ⟨(hpairs q).mpr ⟨a,ha,b,hb,hc⟩,(he q).mpr ⟨a,b,ha,hb,hbn,hc⟩⟩

def TotalPreorder (hM : FirstOrder.Theory.Models M nativeZF) (w Q : M.Carrier .set) : Prop :=
  (∀ q, (Project.FirstOrderSemantics.reduct M).mem q Q → Le hM w q q) ∧
  (∀ q r s, Le hM w q r → Le hM w r s → Le hM w q s) ∧
  (∀ q r, (Project.FirstOrderSemantics.reduct M).mem q Q →
    (Project.FirstOrderSemantics.reduct M).mem r Q → Le hM w q r ∨ Le hM w r q)

def totalPreorder {m : Nat} (w Q : Fin m) : Project.Formula 1 m :=
  .conj (.forallE (.imp (.mem (.bound 0) (.bound Q.succ)) (le w.succ 0 0)))
    (.conj (.forallE (.forallE (.forallE (.imp (le w.succ.succ.succ 2 1)
      (.imp (le w.succ.succ.succ 1 0) (le w.succ.succ.succ 2 0))))))
      (.forallE (.forallE (.imp (.mem (.bound 1) (.bound Q.succ.succ))
        (.imp (.mem (.bound 0) (.bound Q.succ.succ))
          (.disj (le w.succ.succ 1 0) (le w.succ.succ 0 1)))))))

theorem totalPreorder_freeClosed {m : Nat} (w Q : Fin m) : (totalPreorder w Q).FreeClosed := by
  simp -implicitDefEqProofs [totalPreorder,Definitional.Formula.FreeClosed,le_freeClosed]

theorem totalPreorder_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q : Fin m) :
    Project.Formula.satisfies env (totalPreorder w Q) ↔ TotalPreorder hM (env.bound w) (env.bound Q) := by
  simp only [totalPreorder,TotalPreorder,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    le_semantics hM,Project.Term.eval_bound]
  rfl

theorem total_preorder (hM : FirstOrder.Theory.Models M nativeZF) {w Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) : TotalPreorder hM w Q :=
  ⟨fun q hq => le_refl hM hw ((hQ q).mp hq),fun _ _ _ => le_trans hM hw,
    fun q r hq hr => le_total hM hw ((hQ q).mp hq) ((hQ r).mp hr)⟩

/-- The previously constructed source weight values lie in this exact carrier. -/
theorem proper_in_carrier {w Q q : M.Carrier .set} (hQ : Carrier w Q)
    (hq : ConstructionBaseWeights.ProperFraction w q) : (Project.FirstOrderSemantics.reduct M).mem q Q := by
  obtain ⟨a,b,ha,hb,hq,_,hab⟩ := hq
  exact (hQ q).mpr ⟨a,b,ha,hb,⟨a,hab⟩,hq⟩

theorem weights_in_carrier (hM : FirstOrder.Theory.Models M nativeZF) {w one two three h c Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : ConstructionBaseWeights.Digits w one two three)
    (hh : ConstructionBaseWeights.Graph hM true w one two one h)
    (hc : ConstructionBaseWeights.Graph hM false w one two three c) (hQ : Carrier w Q) :
    (∀ n q, PureKuratowski.PairMember M n q h → (Project.FirstOrderSemantics.reduct M).mem q Q) ∧
    (∀ n q, PureKuratowski.PairMember M n q c → (Project.FirstOrderSemantics.reduct M).mem q Q) := by
  have hp := ConstructionBaseWeights.weights_proper hM hw hd hh hc
  exact ⟨fun n q h => proper_in_carrier hQ (hp.1 n q h),fun n q h => proper_in_carrier hQ (hp.2 n q h)⟩

/-- Native unit products identify cross comparison with the donor unit-fraction order. -/
theorem mul_one (hM : FirstOrder.Theory.Models M nativeZF) {w a one : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) : Mul hM a one a ∧ Mul hM one a a := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨p,_,hp⟩ := mul_exists hM hw ha ho
  have he := ZF.ordinalMultiplication_one_right hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF a ha) hone hp
  have h := he ▸ hp
  exact ⟨h,mul_comm hM hw ha ho h⟩

theorem unit_fraction_order (hM : FirstOrder.Theory.Models M nativeZF) {w one p t q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hq : Coordinates w q one p) (hr : Coordinates w r one t) : Le hM w q r ↔ NatLe t p := by
  have ht := (mul_one hM hw hr.2.1 hq.1 hone).2
  have hp := (mul_one hM hw hq.2.1 hq.1 hone).2
  rw [le_iff_cross hM hq hr]
  constructor
  · rintro ⟨u,v,hu,hv,h⟩
    have eu := mul_unique hM hw hr.2.1 hu ht
    have ev := mul_unique hM hw hq.2.1 hv hp
    exact eu ▸ ev ▸ h
  · exact fun h => ⟨t,p,ht,hp,h⟩

def unitOrderSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isOrdinalOne (.bound 1))
      (.imp (coordinates (0 : Fin 6) 4 1 2) (.imp (coordinates (0 : Fin 6) 5 1 3)
        (.iff (le (0 : Fin 6) 4 5)
          (.disj (Project.Formula.extensionalEq (.bound 3) (.bound 2)) (.mem (.bound 3) (.bound 2))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,coordinates_freeClosed,le_freeClosed]

theorem unitOrder_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence unitOrderSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) unitOrderSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,coordinates_semantics hM,
    Project.Formula.satisfies_iff_iff,le_semantics hM,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  exact fun hw hone hq hr => unit_fraction_order hM hw hone hq hr

theorem unitOrder_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence unitOrderSentence) := ModelTransfer.derives (fun _ hM => unitOrder_models hM)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.conj (carrier (1 : Fin 2) 0)
      (.conj (totalPreorder (1 : Fin 2) 0)
        (.forallE (.imp (ConstructionBaseWeights.properFraction (2 : Fin 3) 0) (.mem (.bound 0) (.bound 1))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed,
    totalPreorder_freeClosed,ConstructionBaseWeights.properFraction_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    carrier_semantics hM,totalPreorder_semantics hM,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,ConstructionBaseWeights.properFraction_semantics hM,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  obtain ⟨Q,hQ⟩ := exists_carrier hM (bound 0)
  exact ⟨Q,hQ,total_preorder hM hw hQ,fun _ => proper_in_carrier hQ⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionFractionOrder
