/- Interpret the pinned Base.height/cost fraction graphs as principal cuts.
The old exact exponent offsets n+1 and n+3 are preserved. This supplies actual
set-valued graphs on internal omega; real arithmetic and margin remain separate. -/
import PPAC.Migration.ConstructionRealCuts
import PPAC.Migration.ForcingSupportSize

namespace PPAC.Migration.ConstructionCutWeights
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    (w one two offset Q n c : M.Carrier .set) : Prop :=
  ∃ q, ConstructionBaseWeights.Weight hM height w one two offset n q ∧ Principal hM w Q q c

def value {m : Nat} (height : Bool) (w one two offset Q n c : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ConstructionBaseWeights.weight height w.succ one.succ two.succ offset.succ n.succ 0)
    (principal w.succ Q.succ 0 c.succ))

theorem value_freeClosed {m : Nat} (height : Bool) (w one two offset Q n c : Fin m) :
    (value height w one two offset Q n c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionBaseWeights.weight_freeClosed,principal_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (height : Bool) (w one two offset Q n c : Fin m) :
    Project.Formula.satisfies env (value height w one two offset Q n c) ↔
      Value hM height (env.bound w) (env.bound one) (env.bound two) (env.bound offset) (env.bound Q) (env.bound n) (env.bound c) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionBaseWeights.weight_semantics hM,principal_semantics hM]
  rfl

def valueSchema (height : Bool) : Project.BinarySchema 5 where
  body := value height 2 3 4 5 6 1 0
  freeClosed := value_freeClosed _ _ _ _ _ _ _ _

theorem valueSchema_semantics (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5) (n c : M.Carrier .set) :
    (valueSchema height).denote env n c ↔
      Value hM height (env.bound 0) (env.bound 1) (env.bound 2) (env.bound 3) (env.bound 4) n c :=
  value_semantics hM ((env.push n).push c) height 2 3 4 5 6 1 0

def Graph (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    (w one two offset Q f : M.Carrier .set) : Prop :=
  ∀ n c, PureKuratowski.PairMember M n c f ↔
    (Project.FirstOrderSemantics.reduct M).mem n w ∧ Value hM height w one two offset Q n c

def RangeCuts (R f : M.Carrier .set) : Prop :=
  ∀ n c, PureKuratowski.PairMember M n c f → (Project.FirstOrderSemantics.reduct M).mem c R

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {height : Bool}
    {w one two offset Q n c d : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ht : (Project.FirstOrderSemantics.reduct M).mem two w) (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hc : Value hM height w one two offset Q n c) (hd : Value hM height w one two offset Q n d) : c = d := by
  obtain ⟨q,hq,hc⟩ := hc
  obtain ⟨r,hr,hd⟩ := hd
  have he := ConstructionBaseWeights.weight_unique hM hw ht ho hq hr
  subst r
  exact principal_unique hM hc hd

theorem exists_graph_with_map (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    {w one two offset Q R : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).mem one w) (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two) (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hrange : ∀ n q, (Project.FirstOrderSemantics.reduct M).mem n w →
      ConstructionBaseWeights.Weight hM height w one two offset n q → (Project.FirstOrderSemantics.reduct M).mem q Q) :
    ∃ f, ForcingSupportSize.MapsTo w R f ∧ Graph hM height w one two offset Q f ∧ RangeCuts R f := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases w (Fin.cases one (Fin.cases two (Fin.cases offset (fun _ => Q)))), free := fun _ => w }
  have hValueRange : ∀ n c, (Project.FirstOrderSemantics.reduct M).mem n w →
      Value hM height w one two offset Q n c → (Project.FirstOrderSemantics.reduct M).mem c R := by
    rintro n c hn ⟨q,hq,hc⟩
    exact (hR c).mpr (principal_cut hM hw hQ (hrange n q hn hq) hc)
  obtain ⟨f,hMap,hf⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (valueSchema height) env (source := w) (target := R) (by
      intro n hn
      obtain ⟨q,hq⟩ := ConstructionBaseWeights.weight_exists hM height hw hone ht htn ho hn
      obtain ⟨c,hc⟩ := exists_principal hM w Q q
      exact ⟨c,(valueSchema_semantics hM height env n c).mpr ⟨q,hq,hc⟩⟩) (by
      intro n _ c d hc hd
      exact value_unique hM hw ht ho ((valueSchema_semantics hM height env n c).mp hc)
        ((valueSchema_semantics hM height env n d).mp hd)) (by
      intro n c hn hc
      exact hValueRange n c hn ((valueSchema_semantics hM height env n c).mp hc))
  have hg : Graph hM height w one two offset Q f := fun n c =>
    (hf n c).trans (and_congr Iff.rfl (valueSchema_semantics hM height env n c))
  exact ⟨f,(ForcingSupportSize.native_mapsTo hM w R f).mpr hMap,hg,fun n c hc => hValueRange n c ((hg n c).mp hc).1 ((hg n c).mp hc).2⟩

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) (height : Bool)
    {w one two offset Q R : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hone : (Project.FirstOrderSemantics.reduct M).mem one w) (ht : (Project.FirstOrderSemantics.reduct M).mem two w)
    (htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two) (ho : (Project.FirstOrderSemantics.reduct M).mem offset w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hrange : ∀ n q, (Project.FirstOrderSemantics.reduct M).mem n w →
      ConstructionBaseWeights.Weight hM height w one two offset n q → (Project.FirstOrderSemantics.reduct M).mem q Q) :
    ∃ f, Graph hM height w one two offset Q f ∧ RangeCuts R f := by
  obtain ⟨f,_,hg,hr⟩ := exists_graph_with_map hM height hw hone ht htn ho hQ hR hrange
  exact ⟨f,hg,hr⟩

def graph {m : Nat} (height : Bool) (w one two offset Q f : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) 0))
    (.conj (.mem (.bound 1) (.bound w.succ.succ))
      (value height w.succ.succ one.succ.succ two.succ.succ offset.succ.succ Q.succ.succ 1 0))))

theorem graph_freeClosed {m : Nat} (height : Bool) (w one two offset Q f : Fin m) :
    (graph height w one two offset Q f).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (height : Bool) (w one two offset Q f : Fin m) :
    Project.Formula.satisfies env (graph height w one two offset Q f) ↔
      Graph hM height (env.bound w) (env.bound one) (env.bound two) (env.bound offset) (env.bound Q) (env.bound f) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    value_semantics hM,Project.Term.eval_bound]
  rfl

def rangeCuts {m : Nat} (R f : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) 0))
    (.mem (.bound 0) (.bound R.succ.succ))))

theorem rangeCuts_freeClosed {m : Nat} (R f : Fin m) : (rangeCuts R f).FreeClosed := by
  simp -implicitDefEqProofs [rangeCuts,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem rangeCuts_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R f : Fin m) :
    Project.Formula.satisfies env (rangeCuts R f) ↔ RangeCuts (env.bound R) (env.bound f) := by
  simp only [rangeCuts,RangeCuts,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  rfl

theorem exists_weights (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ one two three Q R height cost, ConstructionBaseWeights.Digits w one two three ∧
      ConstructionFractionOrder.Carrier w Q ∧ CutCarrier hM w Q R ∧
      Graph hM true w one two one Q height ∧ Graph hM false w one two three Q cost ∧
      RangeCuts R height ∧ RangeCuts R cost := by
  obtain ⟨one,two,three,h,c,hd,hh,hc⟩ := ConstructionBaseWeights.exists_weights hM hw
  obtain ⟨Q,hQ⟩ := ConstructionFractionOrder.exists_carrier hM w
  obtain ⟨R,hR⟩ := exists_cutCarrier hM w Q
  have hRange := ConstructionFractionOrder.weights_in_carrier hM hw hd hh hc hQ
  have htn : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a two := ⟨one,hd.2.2.2.2.1.predecessor_mem⟩
  obtain ⟨height,hhg,hhr⟩ := exists_graph hM true hw hd.1 hd.2.1 htn hd.1 hQ hR
    (fun n q hn hq => hRange.1 n q ((hh n q).mpr ⟨hn,hq⟩))
  obtain ⟨cost,hcg,hcr⟩ := exists_graph hM false hw hd.1 hd.2.1 htn hd.2.2.1 hQ hR
    (fun n q hn hq => hRange.2 n q ((hc n q).mpr ⟨hn,hq⟩))
  exact ⟨one,two,three,Q,R,height,cost,hd,hQ,hR,hhg,hcg,hhr,hcr⟩

/-- Strict positivity and strict upper bound, in the cut inclusion order. -/
def BoundedPositive (c unit : M.Carrier .set) : Prop :=
  (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c unit ∧ ¬ Subset unit c

def boundedPositive {m : Nat} (c unit : Fin m) : Project.Formula 1 m :=
  .conj (.existsE (.mem (.bound 0) (.bound c.succ)))
    (.conj (Project.Formula.subset (.bound c) (.bound unit)) (.neg (Project.Formula.subset (.bound unit) (.bound c))))

theorem boundedPositive_freeClosed {m : Nat} (c unit : Fin m) : (boundedPositive c unit).FreeClosed := by
  simp -implicitDefEqProofs [boundedPositive,Definitional.Formula.FreeClosed]

theorem boundedPositive_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (c unit : Fin m) : Project.Formula.satisfies env (boundedPositive c unit) ↔
      BoundedPositive (env.bound c) (env.bound unit) := by
  simp only [boundedPositive,BoundedPositive,ConstructionRealCuts.Subset,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound]
  rfl

theorem proper_cut_bounds (hM : FirstOrder.Theory.Models M nativeZF) {w Q one q unitCode c unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hu : ConstructionFractionOrder.Coordinates w unitCode one one) (hunit : Principal hM w Q unitCode unit)
    (hq : ConstructionBaseWeights.ProperFraction w q) (hc : Principal hM w Q q c) : BoundedPositive c unit := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨a,b,ha,hb,hcode,han,hab⟩ := hq
  have hqC : ConstructionFractionOrder.Coordinates w q a b := ⟨ha,hb,⟨a,hab⟩,hcode⟩
  have hqQ := (hQ q).mpr ⟨a,b,hqC⟩
  have huQ := (hQ unitCode).mpr ⟨one,one,hu⟩
  have hqa := (ConstructionFractionOrder.mul_one hM hw ha hu.1 hone).1
  have hub := (ConstructionFractionOrder.mul_one hM hw hb hu.1 hone).2
  have hlt := (ConstructionFractionDensity.lt_iff_products hM hw hqC hu hqa hub).mpr hab
  obtain ⟨zero,hz,hzw⟩ := hw.1.1
  obtain ⟨zeroCode,hzeroCode⟩ := KuratowskiZF.exists_code hM zero one
  have hzC : ConstructionFractionOrder.Coordinates w zeroCode zero one := ⟨hzw,hu.1,hu.2.2.1,hzeroCode⟩
  have hm0 : ConstructionFractionOrder.Mul hM b zero zero :=
    (ZF.ordinalMultiplication_zero_iff hZF (KuratowskiZF.interpretation hM) (hw.members_areOrdinals hZF b hb) hz).mpr hz
  have h0m := ConstructionFractionOrder.mul_comm hM hw hb hzw hm0
  have hza := (hw.members_areOrdinals hZF a ha).empty_mem_of_nonempty (ZF.modelsKP hZF) han hz
  have hzq := (ConstructionFractionDensity.lt_iff_products hM hw hzC hqC h0m hqa).mpr hza
  exact ⟨⟨zeroCode,(hc zeroCode).mpr ⟨(hQ zeroCode).mpr ⟨zero,one,hzC⟩,hzq⟩⟩,
    (principal_subset_iff hM hw hQ hqQ huQ hc hunit).mpr hlt.1,
    fun h => hlt.2 ((principal_subset_iff hM hw hQ huQ hqQ hunit hc).mp h)⟩

def RangeBound (unit f : M.Carrier .set) : Prop :=
  ∀ n c, PureKuratowski.PairMember M n c f → BoundedPositive c unit

def rangeBound {m : Nat} (unit f : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) 0))
    (boundedPositive 0 unit.succ.succ)))

theorem rangeBound_freeClosed {m : Nat} (unit f : Fin m) : (rangeBound unit f).FreeClosed := by
  simp -implicitDefEqProofs [rangeBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,boundedPositive_freeClosed]

theorem rangeBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (unit f : Fin m) :
    Project.Formula.satisfies env (rangeBound unit f) ↔ RangeBound (env.bound unit) (env.bound f) := by
  simp only [rangeBound,RangeBound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,boundedPositive_semantics]
  rfl

theorem weights_bounded (hM : FirstOrder.Theory.Models M nativeZF) {w one two three Q height cost unitCode unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : ConstructionBaseWeights.Digits w one two three)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hu : ConstructionFractionOrder.Coordinates w unitCode one one) (hunit : Principal hM w Q unitCode unit)
    (hh : Graph hM true w one two one Q height) (hc : Graph hM false w one two three Q cost) :
    RangeBound unit height ∧ RangeBound unit cost := by
  have hon : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z one := hu.2.2.1
  have hthn : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z three := ⟨two,hd.2.2.2.2.2.predecessor_mem⟩
  constructor
  · intro n c hnc
    obtain ⟨hn,q,hq,hprincipal⟩ := (hh n c).mp hnc
    exact proper_cut_bounds hM hw hQ hd.2.2.2.1 hu hunit
      (ConstructionBaseWeights.weight_proper hM hw hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.1 hon hn hq) hprincipal
  · intro n c hnc
    obtain ⟨hn,q,hq,hprincipal⟩ := (hc n c).mp hnc
    exact proper_cut_bounds hM hw hQ hd.2.2.2.1 hu hunit
      (ConstructionBaseWeights.weight_proper hM hw hd.2.2.2.1 hd.2.1 hd.2.2.2.2.1.predecessor_mem hd.2.2.1 hthn hn hq) hprincipal

theorem exists_bounded_weights (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ one two three Q R height cost unitCode unit, ConstructionBaseWeights.Digits w one two three ∧
      ConstructionFractionOrder.Carrier w Q ∧ CutCarrier hM w Q R ∧
      Graph hM true w one two one Q height ∧ Graph hM false w one two three Q cost ∧
      RangeCuts R height ∧ RangeCuts R cost ∧ ConstructionFractionOrder.Coordinates w unitCode one one ∧
      Principal hM w Q unitCode unit ∧ (Project.FirstOrderSemantics.reduct M).mem unit R ∧
      RangeBound unit height ∧ RangeBound unit cost := by
  obtain ⟨one,two,three,Q,R,height,cost,hd,hQ,hR,hh,hc,hhr,hcr⟩ := exists_weights hM hw
  have hon : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z one := by
    obtain ⟨zero,_,hs⟩ := hd.2.2.2.1
    exact ⟨zero,hs.predecessor_mem⟩
  obtain ⟨unitCode,huc⟩ := KuratowskiZF.exists_code hM one one
  have hu : ConstructionFractionOrder.Coordinates w unitCode one one := ⟨hd.1,hd.1,hon,huc⟩
  obtain ⟨unit,hunit⟩ := exists_principal hM w Q unitCode
  have hur := (hR unit).mpr (principal_cut hM hw hQ ((hQ unitCode).mpr ⟨one,one,hu⟩) hunit)
  have hb := weights_bounded hM hw hd hQ hu hunit hh hc
  exact ⟨one,two,three,Q,R,height,cost,unitCode,unit,hd,hQ,hR,hh,hc,hhr,hcr,hu,hunit,hur,hb⟩

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBaseWeights.digits (9 : Fin 10) 8 7 6)
        (.conj (ConstructionFractionOrder.carrier (9 : Fin 10) 5)
        (.conj (cutCarrier (9 : Fin 10) 5 4)
        (.conj (graph true (9 : Fin 10) 8 7 8 5 3)
        (.conj (graph false (9 : Fin 10) 8 7 6 5 2)
        (.conj (rangeCuts (4 : Fin 10) 3)
        (.conj (rangeCuts (4 : Fin 10) 2)
        (.conj (ConstructionFractionOrder.coordinates (9 : Fin 10) 1 8 8)
        (.conj (principal (9 : Fin 10) 5 1 0)
        (.conj (.mem (.bound 0) (.bound 4))
        (.conj (rangeBound (0 : Fin 10) 3)
        (rangeBound (0 : Fin 10) 2))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBaseWeights.digits_freeClosed,
    ConstructionFractionOrder.carrier_freeClosed,cutCarrier_freeClosed,graph_freeClosed,rangeCuts_freeClosed,
    ConstructionFractionOrder.coordinates_freeClosed,principal_freeClosed,rangeBound_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionBaseWeights.digits_semantics,ConstructionFractionOrder.carrier_semantics hM,
    cutCarrier_semantics hM,graph_semantics hM,rangeCuts_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    principal_semantics hM,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,rangeBound_semantics hM]
  exact exists_bounded_weights hM hw

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionCutWeights
