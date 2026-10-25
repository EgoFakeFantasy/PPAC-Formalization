/- Pinned Diagrams.sub_one/sub_sub/index_unique and Diagram.PartialOrder.
The multiplication and unit are internal sets. The exact source left-cancel
monoid/conical assumptions remain explicit; stage 8 must construct them. -/
import PPAC.Migration.ForcingDiagramOrder

namespace PPAC.Migration.ForcingDiagramPoset
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingDiagramOrder (Product product product_semantics Sub sub sub_semantics Le le le_semantics LeftInjection leftInjection leftInjection_semantics)
open ForcingSupportSize (Injection)
open ForcingConditionGraphs
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Unit (D mul e : M.Carrier .set) : Prop :=
  (Definitional.Project.FirstOrderSemantics.reduct M).mem e D ∧
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x D → ∀ y,
    (Product mul e x y ↔ y = x) ∧ (Product mul x e y ↔ y = x)

def Associative (D mul : M.Carrier .set) : Prop :=
  ∀ a b c ab bc z, (Definitional.Project.FirstOrderSemantics.reduct M).mem a D →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem b D →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem c D →
    Product mul a b ab → Product mul b c bc → (Product mul ab c z ↔ Product mul a bc z)

def LeftCancelMonoid (D mul e : M.Carrier .set) : Prop := Unit D mul e ∧
  (∀ n, (Definitional.Project.FirstOrderSemantics.reduct M).mem n D → LeftInjection D mul n) ∧ Associative D mul

def Conical (D mul e : M.Carrier .set) : Prop :=
  ∀ n m, (Definitional.Project.FirstOrderSemantics.reduct M).mem n D →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem m D → Product mul n m e → n = e ∧ m = e

theorem injection_ext (hM : FirstOrder.Theory.Models M nativeZF) {D I r s : M.Carrier .set}
    (hr : Injection D I r) (hs : Injection D I s)
    (he : ∀ x y, PureKuratowski.PairMember M x y r ↔ PureKuratowski.PairMember M x y s) : r = s :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM D I r).mp hr.1).1.1
    ((ForcingSupportSize.native_mapsTo hM D I s).mp hs.1).1.1 he

theorem sub_one {D I mul e r : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hr : Injection D I r) : Sub D mul r e r := by
  intro x z
  constructor
  · intro hxz
    have hx := function_input hr.1.1 hxz
    exact ⟨hx, x, hx, ((h.1.2 x hx x).1).mpr rfl, hxz⟩
  · rintro ⟨hx, y, _, hy, hyz⟩
    exact (((h.1.2 x hx y).1).mp hy) ▸ hyz

theorem sub_sub {D mul e r s t n m nm : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hn : (Definitional.Project.FirstOrderSemantics.reduct M).mem n D)
    (hm : (Definitional.Project.FirstOrderSemantics.reduct M).mem m D) (hnm : Product mul n m nm)
    (hs : Sub D mul r n s) (ht : Sub D mul s m t) : Sub D mul r nm t := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx, y, hy, hmx, hyz⟩ := (ht x z).mp hxz
    obtain ⟨_, v, hv, hny, hvz⟩ := (hs y z).mp hyz
    exact ⟨hx, v, hv, (h.2.2 n m x nm y v hn hm hx hnm hmx).mpr hny, hvz⟩
  · rintro ⟨hx, v, hv, hnx, hvz⟩
    obtain ⟨y, hy, hmx⟩ := (h.2.1 m hm).1 x hx
    exact (ht x z).mpr ⟨hx, y, hy, hmx, (hs y z).mpr
      ⟨hy, v, hv, (h.2.2 n m x nm y v hn hm hx hnm hmx).mp hnx, hvz⟩⟩

theorem index_unique {D I mul e r s n m : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hr : Injection D I r)
    (hn : (Definitional.Project.FirstOrderSemantics.reduct M).mem n D)
    (hm : (Definitional.Project.FirstOrderSemantics.reduct M).mem m D)
    (hsn : Sub D mul r n s) (hsm : Sub D mul r m s) : n = m := by
  obtain ⟨z, hnz, _⟩ := hr.1.1.2 n hn
  have hez := (hsn e z).mpr ⟨h.1.1, n, hn, ((h.1.2 n hn n).2).mpr rfl, hnz⟩
  obtain ⟨_, y, _, hmy, hyz⟩ := (hsm e z).mp hez
  have hym := ((h.1.2 m hm y).2).mp hmy
  exact hr.2 n m z hnz (hym ▸ hyz)

theorem le_refl {D I mul e r : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hr : Injection D I r) : Le D mul r r := ⟨e, h.1.1, sub_one h hr⟩

theorem le_trans {D mul e r s t : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hrs : Le D mul r s) (hst : Le D mul s t) : Le D mul r t := by
  obtain ⟨n, hn, hs⟩ := hrs
  obtain ⟨m, hm, ht⟩ := hst
  obtain ⟨nm, hnmD, hnm⟩ := (h.2.1 n hn).1 m hm
  exact ⟨nm, hnmD, sub_sub h hn hm hnm hs ht⟩

theorem le_antisymm (hM : FirstOrder.Theory.Models M nativeZF) {D I mul e r s : M.Carrier .set}
    (h : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hr : Injection D I r) (hs : Injection D I s)
    (hrs : Le D mul r s) (hsr : Le D mul s r) : r = s := by
  obtain ⟨n, hn, hsn⟩ := hrs
  obtain ⟨m, hm, hrm⟩ := hsr
  obtain ⟨nm, hnmD, hnm⟩ := (h.2.1 n hn).1 m hm
  have hprod := index_unique h hr hnmD h.1.1 (sub_sub h hn hm hnm hsn hrm) (sub_one h hr)
  have hne := (hc n m hn hm (hprod ▸ hnm)).1
  subst n
  exact injection_ext hM hr hs (fun x y => ((sub_one h hr) x y).trans (hsn x y).symm)

def unit {m : Nat} (D mul e : Fin m) : Formula m :=
  (Formula.mem e D).conj (.all ((Formula.mem (Fin.last m) D.castSucc).imp (.all
    (((product mul.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)).conj
    ((product mul.castSucc.castSucc (Fin.last m).castSucc e.castSucc.castSucc (Fin.last (m+1))).iff
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))))

def associative {m : Nat} (D mul : Fin m) : Formula m :=
  .all (.all (.all (.all (.all (.all ((Formula.mem (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).imp ((Formula.mem (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).imp ((Formula.mem (Fin.last (m+2)).castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).imp ((product mul.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc).imp ((product mul.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc).imp ((product mul.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+5))).iff (product mul.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5))))))))))))))

def leftCancelMonoid {m : Nat} (D mul e : Fin m) : Formula m :=
  (unit D mul e).conj ((Formula.all ((Formula.mem (Fin.last m) D.castSucc).imp
    (leftInjection D.castSucc mul.castSucc (Fin.last m)))).conj (associative D mul))

def conical {m : Nat} (D mul e : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc D.castSucc.castSucc).imp ((Formula.mem (Fin.last (m+1)) D.castSucc.castSucc).imp ((product mul.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) e.castSucc.castSucc).imp ((Formula.equal (Fin.last m).castSucc e.castSucc.castSucc).conj (.equal (Fin.last (m+1)) e.castSucc.castSucc))))))

theorem unit_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul e : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (unit D mul e) ↔
      Unit (env D) (env mul) (env e) := by
  simp only [unit, Unit, Formula.Realize, Source.Formula.iff, product_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun ⟨he,h⟩ => ⟨he,fun x hx y => ⟨⟨(h x hx y).1.1,(h x hx y).1.2⟩,⟨(h x hx y).2.1,(h x hx y).2.2⟩⟩⟩,
    fun ⟨he,h⟩ => ⟨he,fun x hx y => ⟨⟨(h x hx y).1.mp,(h x hx y).1.mpr⟩,⟨(h x hx y).2.mp,(h x hx y).2.mpr⟩⟩⟩⟩

theorem associative_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (associative D mul) ↔
      Associative (env D) (env mul) := by
  simp only [associative, Associative, Formula.Realize, Source.Formula.iff, product_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h a b c ab bc z ha hb hc hab hbc => ⟨(h a b c ab bc z ha hb hc hab hbc).1,(h a b c ab bc z ha hb hc hab hbc).2⟩,
    fun h a b c ab bc z ha hb hc hab hbc => ⟨(h a b c ab bc z ha hb hc hab hbc).mp,(h a b c ab bc z ha hb hc hab hbc).mpr⟩⟩

theorem leftCancelMonoid_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul e : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (leftCancelMonoid D mul e) ↔
      LeftCancelMonoid (env D) (env mul) (env e) := by
  simp only [leftCancelMonoid, LeftCancelMonoid, Formula.Realize, unit_semantics (M := M), associative_semantics (M := M), leftInjection_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

theorem conical_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul e : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (conical D mul e) ↔
      Conical (env D) (env mul) (env e) := by
  simp only [conical, Conical, Formula.Realize, product_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.ForcingDiagramPoset
