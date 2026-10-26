/- Nonnegative differences for the pinned Base.margin height comparison.
Reuse the native ordinal right remainder and existing fraction/principal-cut
addition. This does not identify arbitrary real cuts with rational cuts. -/
import PPAC.Migration.ConstructionPrincipalAddition

namespace PPAC.Migration.ConstructionFractionDifference
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionFractionAddition
open ConstructionRealCuts ConstructionPrincipalAddition
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Multiplying both coordinates preserves the represented fraction. -/
theorem scaled_equiv (hM : FirstOrder.Theory.Models M nativeZF) {w q r a b k ak bk : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Coordinates w q a b) (hr : Coordinates w r ak bk)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k w)
    (hak : Mul hM a k ak) (hbk : Mul hM b k bk) : Le hM w q r ∧ Le hM w r q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨x,_,hx⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨y,_,hy⟩ := mul_exists hM hw hr.1 hq.2.1
  have he := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord a hq.1) (ord k hk) (ord b hq.2.1) hak (mul_comm hM hw hq.2.1 hk hbk) hx hy
  exact ⟨(le_iff_products hM hw hq hr hx hy).mpr (Or.inl he),
    (le_iff_products hM hw hr hq hy hx).mpr (Or.inl he.symm)⟩

/-- Sum with a common denominator agrees with adding its numerators. -/
theorem same_den_sum (hM : FirstOrder.Theory.Models M nativeZF) {w q r t s a b d n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Coordinates w q a d) (hr : Coordinates w r b d) (ht : Coordinates w t n d)
    (hn : Add hM a b n) (hs : Sum hM w q r s) : Le hM w s t ∧ Le hM w t s := by
  obtain ⟨a',d',b',d'',n',den,hq',hr',hs,u,v,hu,hv,hn',hden⟩ := hs
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq.2.2.2 hq'.2.2.2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
  obtain ⟨nd,_,hnd⟩ := mul_exists hM hw ht.1 ht.2.1
  have hadd := mul_add hM hw hq.2.1 hq.1 hr.1 hn (mul_comm hM hw ht.1 ht.2.1 hnd)
    (mul_comm hM hw hq.1 hq.2.1 hu) (mul_comm hM hw hr.1 hr.2.1 hv)
  have he := ConstructionBaseMonoid.addition_unique hM hw (mul_range hM hw hr.1 hr.2.1 hv) hn' hadd
  subst nd
  have hh := scaled_equiv hM hw ht hs ht.2.1 hnd hden
  exact ⟨hh.2,hh.1⟩

theorem natural_remainder (hM : FirstOrder.Theory.Models M nativeZF) {w a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a w) (hb : (Project.FirstOrderSemantics.reduct M).mem b w)
    (hab : NatLe a b) : ∃ g, (Project.FirstOrderSemantics.reduct M).mem g w ∧ Add hM a g b := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  rcases hab with he | hab
  · subst b
    obtain ⟨zero,hz,hzw⟩ := hw.1.1
    exact ⟨zero,hzw,(ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩
  · obtain ⟨g,hg,_⟩ := ZF.ordinalAddition_existsUnique_rightRemainder hZF I
      (hw.members_areOrdinals hZF a ha) (hw.members_areOrdinals hZF b hb) hab
    refine ⟨g,?_,hg⟩
    rcases ZF.ordinalAddition_right_eq_or_mem hZF I (hw.members_areOrdinals hZF a ha) hg.right_isOrdinal hg with he | hgb
    · exact he ▸ hb
    · exact hw.transitive hZF b hb g hgb

/-- Every ordered pair of internal fractions has a nonnegative additive gap. -/
theorem difference_exists (hM : FirstOrder.Theory.Models M nativeZF) {w q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hqr : Le hM w q r) :
    ∃ gap s, Fraction w gap ∧ Sum hM w q gap s ∧ Le hM w s r ∧ Le hM w r s := by
  have hqrCopy := hqr
  obtain ⟨a,b,c,d,hq,hr,ad,cb,had,hcb,hle⟩ := hqrCopy
  have hAd := mul_range hM hw hq.1 hr.2.1 had
  have hCb := mul_range hM hw hr.1 hq.2.1 hcb
  obtain ⟨g,hg,hgap⟩ := natural_remainder hM hw hAd hCb hle
  obtain ⟨bd,hBd,hbd⟩ := mul_exists hM hw hq.2.1 hr.2.1
  have hBdn := mul_nonempty hM hw hq.2.1 hr.2.1 hq.2.2.1 hr.2.2.1 hbd
  obtain ⟨q',hq'code⟩ := KuratowskiZF.exists_code hM ad bd
  obtain ⟨r',hr'code⟩ := KuratowskiZF.exists_code hM cb bd
  obtain ⟨gap,hgapCode⟩ := KuratowskiZF.exists_code hM g bd
  have hq' : Coordinates w q' ad bd := ⟨hAd,hBd,hBdn,hq'code⟩
  have hr' : Coordinates w r' cb bd := ⟨hCb,hBd,hBdn,hr'code⟩
  have hg' : Coordinates w gap g bd := ⟨hg,hBd,hBdn,hgapCode⟩
  have eqQ := scaled_equiv hM hw hq hq' hr.2.1 had hbd
  have eqR := scaled_equiv hM hw hr hr' hq.2.1 hcb (mul_comm hM hw hq.2.1 hr.2.1 hbd)
  obtain ⟨s,hs⟩ := sum_exists hM hw ⟨a,b,hq⟩ ⟨g,bd,hg'⟩
  obtain ⟨s',hs'⟩ := sum_exists hM hw ⟨ad,bd,hq'⟩ ⟨g,bd,hg'⟩
  have hgrefl := le_refl hM hw ⟨g,bd,hg'⟩
  have eqS := sum_equiv hM hw hs hs' eqQ ⟨hgrefl,hgrefl⟩
  have eqR' := same_den_sum hM hw hq' hg' hr' hgap hs'
  exact ⟨gap,s,⟨g,bd,hg'⟩,hs,
    le_trans hM hw eqS.1 (le_trans hM hw eqR'.1 eqR.2),
    le_trans hM hw eqR.1 (le_trans hM hw eqR'.2 eqS.2)⟩

/-- In the actual cut representation, adding the gap gives exactly the endpoint. -/
theorem principal_difference_exists (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hc : Represented hM w Q c) (hd : Represented hM w Q d) (hcd : Subset c d) :
    ∃ gap, Represented hM w Q gap ∧ PrincipalAdd hM w Q c gap d := by
  obtain ⟨q,hq,hc⟩ := hc
  obtain ⟨r,hr,hd⟩ := hd
  have hqr := (principal_subset_iff hM hw hQ hq hr hc hd).mp hcd
  obtain ⟨g,s,hg,hs,hsr,hrs⟩ := difference_exists hM hw hqr
  obtain ⟨gap,hgap⟩ := exists_principal hM w Q g
  obtain ⟨e,he⟩ := exists_principal hM w Q s
  have hsrCopy := hsr
  obtain ⟨a,b,a',b',hsc,_,_⟩ := hsrCopy
  have hed : e = d := (principal_eq_iff hM hw hQ ((hQ s).mpr ⟨a,b,hsc⟩) hr he hd).mpr ⟨hsr,hrs⟩
  subst e
  exact ⟨gap,⟨g,(hQ g).mpr hg,hgap⟩,q,g,s,hq,(hQ g).mpr hg,hc,hgap,hs,he⟩

theorem principal_difference_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d gap gap' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hg : PrincipalAdd hM w Q c gap d) (hg' : PrincipalAdd hM w Q c gap' d) : gap = gap' := by
  have h1 := ConstructionPrincipalAddition.add_comm hM hw hg
  have h2 := ConstructionPrincipalAddition.add_comm hM hw hg'
  have le1 := (ConstructionPrincipalAddition.add_le_iff hM hw hQ h1 h2).mp (fun _ h => h)
  have le2 := (ConstructionPrincipalAddition.add_le_iff hM hw hQ h2 h1).mp (fun _ h => h)
  exact (ModelTransfer.extensionality hM).eq_of_same_members gap gap' (fun p => ⟨le1 p,le2 p⟩)

theorem sum_zero (hM : FirstOrder.Theory.Models M nativeZF) {w q z zero one : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Fraction w q)
    (hz : Coordinates w z zero one) (hzero : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) : Sum hM w q z q := by
  obtain ⟨a,b,hq⟩ := hq
  have hZF := ModelTransfer.project_models_iff.mp hM
  have h0 : Mul hM b zero zero := (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF b hq.2.1) hzero).mpr hzero
  exact ⟨a,b,zero,one,a,b,hq,hz,hq,a,zero,(mul_one hM hw hq.1 hz.2.1 hone).1,
    mul_comm hM hw hq.2.1 hz.1 h0,(ZF.ordinalAddition_zero_iff hZF (KuratowskiZF.interpretation hM) hzero).mpr rfl,
    (mul_one hM hw hq.2.1 hz.2.1 hone).1⟩

theorem zero_le (hM : FirstOrder.Theory.Models M nativeZF) {w q z zero one : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hq : Fraction w q)
    (hz : Coordinates w z zero one) (hzero : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) : Le hM w z q := by
  obtain ⟨a,b,hq⟩ := hq
  have hZF := ModelTransfer.project_models_iff.mp hM
  have h0 : Mul hM b zero zero := (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM)
    (hw.members_areOrdinals hZF b hq.2.1) hzero).mpr hzero
  have ha : NatLe zero a := by
    rcases nat_compare hM hw hz.1 hq.1 with he | hza | haz
    · exact Or.inl he
    · exact Or.inr hza
    · exact (hzero a haz).elim
  exact (le_iff_products hM hw hz hq (mul_comm hM hw hq.2.1 hz.1 h0) (mul_one hM hw hq.1 hz.2.1 hone).1).mpr ha

/-- The zero cut is the actual empty set and is an additive identity. -/
theorem principal_zero_exists (hM : FirstOrder.Theory.Models M nativeZF) {w Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) :
    ∃ zcut, (∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zcut) ∧
      Represented hM w Q zcut ∧ ∀ c, Represented hM w Q c → PrincipalAdd hM w Q c zcut c := by
  obtain ⟨zero,hzero,hzw⟩ := hw.1.1
  obtain ⟨one,hs,how⟩ := hw.1.2 zero hzw
  have hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one := ⟨zero,hzero,hs⟩
  obtain ⟨z,hzCode⟩ := KuratowskiZF.exists_code hM zero one
  have hz : Coordinates w z zero one := ⟨hzw,how,⟨zero,hs.predecessor_mem⟩,hzCode⟩
  have hzQ := (hQ z).mpr ⟨zero,one,hz⟩
  obtain ⟨zcut,hzcut⟩ := exists_principal hM w Q z
  refine ⟨zcut,?_,⟨z,hzQ,hzcut⟩,?_⟩
  · intro p hp
    have hh := (hzcut p).mp hp
    exact hh.2.2 (zero_le hM hw ((hQ p).mp hh.1) hz hzero hone)
  · rintro c ⟨q,hq,hc⟩
    exact ⟨q,z,q,hq,hzQ,hc,hzcut,sum_zero hM hw ((hQ q).mp hq) hz hzero hone,hc⟩

theorem strict_difference_positive (hM : FirstOrder.Theory.Models M nativeZF) {w Q c d gap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hc : Represented hM w Q c) (hg : PrincipalAdd hM w Q c gap d) (hstrict : ¬ Subset d c) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p gap := by
  classical
  obtain ⟨zero,_,_,hidentity⟩ := principal_zero_exists hM hw hQ
  apply Classical.byContradiction
  intro hn
  have hsub : Subset gap zero := fun p hp => (hn ⟨p,hp⟩).elim
  exact hstrict ((ConstructionPrincipalAddition.add_le_iff hM hw hQ
    (ConstructionPrincipalAddition.add_comm hM hw hg)
    (ConstructionPrincipalAddition.add_comm hM hw (hidentity c hc))).mpr hsub)

def differenceLaw {m : Nat} (w Q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (represented w.succ.succ Q.succ.succ 1)
    (.imp (represented w.succ.succ Q.succ.succ 0) (.imp (Project.Formula.subset (.bound 1) (.bound 0))
      (.existsE (.conj (represented w.succ.succ.succ Q.succ.succ.succ 0)
        (.conj (principalAdd w.succ.succ.succ Q.succ.succ.succ 2 0 1)
          (.conj (.forallE (.imp (principalAdd w.succ.succ.succ.succ Q.succ.succ.succ.succ 3 0 2)
            (Project.Formula.extensionalEq (.bound 0) (.bound 1))))
            (.imp (.neg (Project.Formula.subset (.bound 1) (.bound 2))) (.existsE (.mem (.bound 0) (.bound 1))))))))))))

theorem differenceLaw_freeClosed {m : Nat} (w Q : Fin m) : (differenceLaw w Q).FreeClosed := by
  simp -implicitDefEqProofs [differenceLaw,Definitional.Formula.FreeClosed,represented_freeClosed,principalAdd_freeClosed]

theorem differenceLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q : Fin m) :
    Project.Formula.satisfies env (differenceLaw w Q) ↔ ∀ c d,
      Represented hM (env.bound w) (env.bound Q) c → Represented hM (env.bound w) (env.bound Q) d → Subset c d →
      ∃ gap, Represented hM (env.bound w) (env.bound Q) gap ∧ PrincipalAdd hM (env.bound w) (env.bound Q) c gap d ∧
        (∀ g, PrincipalAdd hM (env.bound w) (env.bound Q) c g d → g = gap) ∧
        (¬ Subset d c → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p gap) := by
  simp only [differenceLaw,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    represented_semantics hM,principalAdd_semantics hM,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionRealCuts.Subset]
  rfl

def differenceSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 2 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (carrier (0 : Fin 2) 1) (differenceLaw (0 : Fin 2) 1)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed,differenceLaw_freeClosed]

theorem difference_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence differenceSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) differenceSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    carrier_semantics hM,differenceLaw_semantics hM]
  intro hw hQ c d hc hd hcd
  obtain ⟨gap,hgap,hadd⟩ := principal_difference_exists hM hw hQ hc hd hcd
  exact ⟨gap,hgap,hadd,fun _ h => principal_difference_unique hM hw hQ h hadd,
    fun h => strict_difference_positive hM hw hQ hc hadd h⟩

theorem difference_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence differenceSentence) := ModelTransfer.derives (fun _ hM => difference_models hM)

end PPAC.Migration.ConstructionFractionDifference
