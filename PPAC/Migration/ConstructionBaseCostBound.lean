/- Pinned MonoidBase.Base.margin, second branch: every missing divisor has
cost at most 2^(-(x+3)). Reuse native exponent monotonicity and the existing
source cost graph. This is not the strict height-gap estimate. -/
import PPAC.Migration.ConstructionCutWeights

namespace PPAC.Migration.ConstructionBaseCostBound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBaseWeights ConstructionFractionOrder ConstructionFractionDensity
open ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem denominator_strict (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two offset n m p t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hot : (Project.FirstOrderSemantics.reduct M).mem one two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hnm : (Project.FirstOrderSemantics.reduct M).mem n m)
    (hp : Denominator hM w two offset n p) (htp : Denominator hM w two offset m t) :
    (Project.FirstOrderSemantics.reduct M).mem p t := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨k,hk,_,hnk,hp⟩ := hp
  obtain ⟨l,hl,_,hml,htp⟩ := htp
  have hkl := ZF.ordinalAddition_isIncreasingOnOrdinals hZF (KuratowskiZF.interpretation hM)
    (ord offset ho) n m (ord n hn) (ord m hm) hnm k l
    (add_comm hM hw hn ho hnk) (add_comm hM hw hm ho hml)
  exact (ZF.ordinalExponentiation_values_mem_iff hZF (KuratowskiZF.interpretation hM)
    (ord two ht) hone hot (ord k hk) (ord l hl) hp htp).mpr hkl

theorem denominator_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two offset n m p t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hot : (Project.FirstOrderSemantics.reduct M).mem one two)
    (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hnm : NatLe n m)
    (hp : Denominator hM w two offset n p) (htp : Denominator hM w two offset m t) : NatLe p t := by
  rcases hnm with he | hnm
  · subst m
    exact Or.inl (denominator_unique hM hw ht ho hp htp)
  · exact Or.inr (denominator_strict hM hw hone ht hot ho hn hm hnm hp htp)

theorem cost_coordinates (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three n q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hq : Weight hM false w one two three n q) :
    ∃ p, Denominator hM w two three n p ∧ Coordinates w q one p := by
  obtain ⟨p,hp,a,ha,he,hq⟩ := hq
  change a = one at he
  subst a
  exact ⟨p,hp,ha,hp.choose_spec.2.1,
    denominator_nonempty hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hp,hq⟩

/-- The source pow_le_pow_of_le_one step, with its exact n+3 offset. -/
theorem cost_antitone (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three n m q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w) (hnm : NatLe n m)
    (hq : Weight hM false w one two three n q) (hr : Weight hM false w one two three m r) :
    Le hM w r q := by
  obtain ⟨p,hp,hq⟩ := cost_coordinates hM hw hd hq
  obtain ⟨t,ht,hr⟩ := cost_coordinates hM hw hd hr
  exact (unit_fraction_order hM hw hd.2.2.2.1 hr hq).mpr
    (denominator_mono hM hw hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.2.2.1 hn hm hnm hp ht)

theorem cut_cost_antitone (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q n m c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w) (hnm : NatLe n m)
    (hc : ConstructionCutWeights.Value hM false w one two three Q n c)
    (hdv : ConstructionCutWeights.Value hM false w one two three Q m d) : Subset d c := by
  obtain ⟨q,hq,hc⟩ := hc
  obtain ⟨r,hr,hdv⟩ := hdv
  obtain ⟨p,_,hqp⟩ := cost_coordinates hM hw hd hq
  obtain ⟨t,_,hrt⟩ := cost_coordinates hM hw hd hr
  exact (principal_subset_iff hM hw hQ ((hQ r).mpr ⟨one,t,hrt⟩) ((hQ q).mpr ⟨one,p,hqp⟩) hdv hc).mpr
    (cost_antitone hM hw hd hn hm hnm hq hr)

/-- Exactly the bound used in the second branch of the source Base.margin. -/
theorem missing_cost_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q cost x d cx cd : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (hcx : PureKuratowski.PairMember M x cx cost) (hcd : PureKuratowski.PairMember M d cd cost)
    (hmissing : ¬ NatLe d x) : Subset cd cx := by
  obtain ⟨hx,hxv⟩ := (hc x cx).mp hcx
  obtain ⟨hdn,hdv⟩ := (hc d cd).mp hcd
  have hxd : NatLe x d := by
    rcases nat_compare hM hw hx hdn with he | hxd | hdx
    · exact (hmissing (Or.inl he.symm)).elim
    · exact Or.inr hxd
    · exact (hmissing (Or.inr hdx)).elim
  exact cut_cost_antitone hM hw hd hQ hx hdn hxd hxv hdv

def natLeF {m : Nat} (a b : Fin m) : Project.Formula 1 m :=
  .disj (Project.Formula.extensionalEq (.bound a) (.bound b)) (.mem (.bound a) (.bound b))

theorem natLeF_freeClosed {m : Nat} (a b : Fin m) : (natLeF a b).FreeClosed := by
  simp -implicitDefEqProofs [natLeF,Definitional.Formula.FreeClosed]

theorem natLeF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (a b : Fin m) :
    Project.Formula.satisfies env (natLeF a b) ↔ NatLe (env.bound a) (env.bound b) := by
  simp only [natLeF,NatLe,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]

def missedValue {m : Nat} (cost x y c : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge cost.succ 0 c.succ))
    (.conj (natLeF 0 y.succ) (.neg (natLeF 0 x.succ))))

theorem missedValue_freeClosed {m : Nat} (cost x y c : Fin m) : (missedValue cost x y c).FreeClosed := by
  simp -implicitDefEqProofs [missedValue,Definitional.Formula.FreeClosed,natLeF_freeClosed,ProjectSyntax.freeClosed]

theorem missedValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (cost x y c : Fin m) :
    Project.Formula.satisfies env (missedValue cost x y c) ↔ ∃ d,
      PureKuratowski.PairMember M d (env.bound c) (env.bound cost) ∧ NatLe d (env.bound y) ∧ ¬ NatLe d (env.bound x) := by
  simp only [missedValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,natLeF_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def MissingFamily (cost x y family : M.Carrier .set) : Prop := ∀ c,
  (Project.FirstOrderSemantics.reduct M).mem c family ↔
    ∃ d, PureKuratowski.PairMember M d c cost ∧ NatLe d y ∧ ¬ NatLe d x

def missingFamily {m : Nat} (cost x y family : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound family.succ)) (missedValue cost.succ x.succ y.succ 0))

theorem missingFamily_freeClosed {m : Nat} (cost x y family : Fin m) :
    (missingFamily cost x y family).FreeClosed := by
  simp -implicitDefEqProofs [missingFamily,Definitional.Formula.FreeClosed,missedValue_freeClosed]

theorem missingFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (cost x y family : Fin m) :
    Project.Formula.satisfies env (missingFamily cost x y family) ↔
      MissingFamily (env.bound cost) (env.bound x) (env.bound y) (env.bound family) := by
  simp only [missingFamily,MissingFamily,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,missedValue_semantics hM]
  rfl

theorem cost_value_cut (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q n c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hc : ConstructionCutWeights.Value hM false w one two three Q n c) : Cut hM w Q c := by
  obtain ⟨q,hq,hc⟩ := hc
  obtain ⟨p,_,hqp⟩ := cost_coordinates hM hw hd hq
  exact principal_cut hM hw hQ ((hQ q).mpr ⟨one,p,hqp⟩) hc

/-- The literal source missed-cost image, with no extra elements from Collection. -/
theorem exists_missing_family (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q R cost x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q cost) :
    ∃ family, MissingFamily cost x y family ∧ Subset family R := by
  let schema : Project.UnarySchema 3 := { body := missedValue 1 2 3 0, freeClosed := missedValue_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases cost (Fin.cases x (fun _ => y)), free := fun _ => w }
  obtain ⟨family,hf⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env R
  have he : ∀ c, Project.Formula.satisfies (env.push c) schema.body ↔
      ∃ d, PureKuratowski.PairMember M d c cost ∧ NatLe d y ∧ ¬ NatLe d x :=
    fun c => missedValue_semantics hM (env.push c) 1 2 3 0
  refine ⟨family,fun c => ⟨fun h => (he c).mp ((hf c).mp h).2,?_⟩,fun c h => ((hf c).mp h).1⟩
  intro h
  obtain ⟨d,hdc,hdy,hdx⟩ := h
  exact (hf c).mpr ⟨(hR c).mpr (cost_value_cut hM hw hd hQ ((hc d c).mp hdc).2),(he c).mpr ⟨d,hdc,hdy,hdx⟩⟩

theorem missing_upper_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q cost x y cx family : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (hcx : PureKuratowski.PairMember M x cx cost) (hf : MissingFamily cost x y family) : UpperBound family cx := by
  intro c hcf
  obtain ⟨d,hdc,_,hmissing⟩ := (hf c).mp hcf
  exact missing_cost_bound hM hw hd hQ hc hcx hdc hmissing

theorem cost_graph_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q cost n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) : ∃ c, PureKuratowski.PairMember M n c cost := by
  obtain ⟨q,hq⟩ := weight_exists hM false hw hd.1 hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hd.2.2.1 hn
  obtain ⟨c,hc'⟩ := exists_principal hM w Q q
  exact ⟨c,(hc n c).mpr ⟨hn,q,hq,hc'⟩⟩

theorem missing_family_nonempty (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q cost x y family : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (hxy : (Project.FirstOrderSemantics.reduct M).mem x y) (hf : MissingFamily cost x y family) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c family := by
  obtain ⟨cy,hcy⟩ := cost_graph_total hM hw hd hc hy
  have hx := hw.transitive (ModelTransfer.project_models_iff.mp hM) y hy x hxy
  exact ⟨cy,(hf cy).mpr ⟨y,hcy,Or.inl rfl,fun h => nat_not_reverse hM hw hx h hxy⟩⟩

/-- Source UniformMargin.supremum_lt's non-strict cost bound, on its exact image. -/
theorem missing_supremum_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three Q cost x y cx : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hQ : Carrier w Q) (hc : ConstructionCutWeights.Graph hM false w one two three Q cost)
    (hcx : PureKuratowski.PairMember M x cx cost)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (hxy : (Project.FirstOrderSemantics.reduct M).mem x y) :
    ∃ family s, MissingFamily cost x y family ∧ (∃ c, (Project.FirstOrderSemantics.reduct M).mem c family) ∧
      Cut hM w Q s ∧ UpperBound family s ∧
      (∀ t, UpperBound family t → Subset s t) ∧ Subset s cx := by
  obtain ⟨R,hR⟩ := exists_cutCarrier hM w Q
  obtain ⟨family,hf,hfR⟩ := exists_missing_family hM hw hd hQ hR hc (x := x) (y := y)
  have hb := missing_upper_bound hM hw hd hQ hc hcx hf
  obtain ⟨s,hs,hu,hl⟩ := bounded_union hM hR hfR (cost_value_cut hM hw hd hQ ((hc x cx).mp hcx).2) hb
  exact ⟨family,s,hf,missing_family_nonempty hM hw hd hc hy hxy hf,hs,hu,hl,hl cx hb⟩

def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 9 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (digits (0 : Fin 9) 1 2 3) (.imp (carrier (0 : Fin 9) 4)
      (.imp (ConstructionCutWeights.graph false (0 : Fin 9) 1 2 3 4 5)
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 9) 6 7))
          (.imp (.mem (.bound 8) (.bound 0)) (.imp (.mem (.bound 6) (.bound 8))
            (.existsE (.existsE (.conj (missingFamily (7 : Fin 11) 8 10 1)
              (.conj (.existsE (.mem (.bound 0) (.bound 2)))
                (.conj (cut (2 : Fin 11) 6 0) (.conj (supremum (1 : Fin 11) 0)
                  (Project.Formula.subset (.bound 0) (.bound 9)))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,digits_freeClosed,
    carrier_freeClosed,ConstructionCutWeights.graph_freeClosed,ProjectSyntax.freeClosed,
    missingFamily_freeClosed,cut_freeClosed,supremum_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    digits_semantics,carrier_semantics hM,ConstructionCutWeights.graph_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    missingFamily_semantics hM,cut_semantics hM,supremum_semantics,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  intro hw hd hQ hc hcx hy hxy
  obtain ⟨f,s,hf,hne,hs,hu,hl,hb⟩ := missing_supremum_bound hM hw hd hQ hc hcx hy hxy
  exact ⟨f,s,hf,hne,hs,⟨hu,hl⟩,hb⟩

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence boundSentence) := ModelTransfer.derives (fun _ hM => bound_models hM)

end PPAC.Migration.ConstructionBaseCostBound
