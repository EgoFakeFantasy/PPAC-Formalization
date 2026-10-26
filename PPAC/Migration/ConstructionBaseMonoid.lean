/- Pinned Construction/MonoidBase.Base: Multiplicative internal omega.
Reuse native ordinal addition and native definable function graphs. This is
only the algebraic part of Base.object; its real height/cost margin is not
assumed or claimed here. Every quantifier ranges over the internal model. -/
import PPAC.Migration.ForcingDiagramPoset
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Ord.Arithmetic.Algebra
import YesMetaZFC.SetTheory.Ord.Arithmetic.Identity
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison

namespace PPAC.Migration.ConstructionBaseMonoid
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Graph of addition on all internal naturals, including nonstandard ones. -/
def AdditionGraph (hM : FirstOrder.Theory.Models M nativeZF) (w mul : M.Carrier .set) : Prop :=
  ∀ x y z, Product mul x y z ↔
    (Project.FirstOrderSemantics.reduct M).mem x w ∧
    (Project.FirstOrderSemantics.reduct M).mem y w ∧
    (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) z x y

def sumPair : Project.BinarySchema 1 where
  body := .existsE (.existsE (.conj (.mem (.bound 1) (.bound 4))
    (.conj (.mem (.bound 0) (.bound 4))
      (.conj (PureKuratowskiProject.code (.bound 3) (.bound 1) (.bound 0))
        (Project.Formula.isOrdinalAddition PureKuratowskiProject.convention (.bound 2) (.bound 1) (.bound 0))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, PureKuratowskiProject.code]

theorem sumPair_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1) (p z : M.Carrier .set) :
    sumPair.denote env p z ↔ ∃ x, (Project.FirstOrderSemantics.reduct M).mem x (env.bound 0) ∧
      ∃ y, (Project.FirstOrderSemantics.reduct M).mem y (env.bound 0) ∧ PureKuratowski.Code M p x y ∧
        (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) z x y := by
  simp only [sumPair, Project.BinarySchema.denote, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    KuratowskiZF.code_correct hM, Project.Formula.satisfies_isOrdinalAddition_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM), Project.Term.eval_bound]
  change (∃ x y, _ ∧ _ ∧ _ ∧ _) ↔ _
  exact ⟨fun ⟨x,y,hx,hy,hp,hz⟩ => ⟨x,hx,y,hy,hp,hz⟩,
    fun ⟨x,hx,y,hy,hp,hz⟩ => ⟨x,y,hx,hy,hp,hz⟩⟩

theorem addition_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w x y a b : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w)
    (ha : (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) a x y)
    (hb : (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) b x y) : a = b := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨s,_,hs⟩ := ZF.ordinalAddition_existsUnique hZF (KuratowskiZF.interpretation hM) x
    (hw.members_areOrdinals hZF y hy)
  exact (hs a ha).trans (hs b hb).symm

theorem exists_additionGraph (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) : ∃ mul, AdditionGraph hM w mul := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨pairs,hpairs⟩ := ZF.exists_cartesianProduct hZF I w w
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 :=
    { bound := fun _ => w, free := fun _ => w }
  obtain ⟨mul,_,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I sumPair env
    (source := pairs) (target := w) (by
      intro p hp
      obtain ⟨x,hx,y,hy,hp⟩ := (hpairs p).mp hp
      obtain ⟨z,hz,_⟩ := ZF.ordinalAddition_existsUnique hZF I x (hw.members_areOrdinals hZF y hy)
      exact ⟨z,(sumPair_semantics hM env p z).mpr ⟨x,hx,y,hy,hp,hz⟩⟩) (by
      intro p _ a b ha hb
      obtain ⟨x,hx,y,hy,hp,ha⟩ := (sumPair_semantics hM env p a).mp ha
      obtain ⟨x',_,y',_,hp',hb⟩ := (sumPair_semantics hM env p b).mp hb
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact addition_unique hM hw hy ha hb) (by
      intro p z _ hz
      obtain ⟨x,hx,y,hy,_,hz⟩ := (sumPair_semantics hM env p z).mp hz
      exact ZF.ordinalAddition_mem_omega hZF I hw hx hy hz)
  refine ⟨mul,fun x y z => ?_⟩
  constructor
  · rintro ⟨p,hp,hpz⟩
    obtain ⟨x',hx,y',hy,hp',hz⟩ := (sumPair_semantics hM env p z).mp ((he p z).mp hpz).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    exact ⟨hx,hy,hz⟩
  · rintro ⟨hx,hy,hz⟩
    obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM x y
    exact ⟨p,hp,(he p z).mpr ⟨(hpairs p).mpr ⟨x,hx,y,hy,hp⟩,
      (sumPair_semantics hM env p z).mpr ⟨x,hx,y,hy,hp,hz⟩⟩⟩

theorem leftCancelMonoid (hM : FirstOrder.Theory.Models M nativeZF)
    {w mul zero : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hg : AdditionGraph hM w mul) (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) : LeftCancelMonoid w mul zero := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  have closed : ∀ {x y z}, Product mul x y z → (Project.FirstOrderSemantics.reduct M).mem z w := by
    intro x y z h
    obtain ⟨hx,hy,ha⟩ := (hg x y z).mp h
    exact ZF.ordinalAddition_mem_omega hZF I hw hx hy ha
  refine ⟨⟨hzw,?_⟩,?_,?_⟩
  · intro x hx y
    constructor
    · constructor
      · intro h
        exact ZF.ordinalAddition_empty_left hZF I hz x (ord x hx) y ((hg zero x y).mp h).2.2
      · intro heq
        subst y
        obtain ⟨s,hs,_⟩ := ZF.ordinalAddition_existsUnique hZF I zero (ord x hx)
        have he := ZF.ordinalAddition_empty_left hZF I hz x (ord x hx) s hs
        exact (hg zero x x).mpr ⟨hzw,hx,he ▸ hs⟩
    · exact (hg x zero y).trans ⟨fun h => (ZF.ordinalAddition_zero_iff hZF I hz).mp h.2.2,
        fun h => ⟨hx,hzw,(ZF.ordinalAddition_zero_iff hZF I hz).mpr h⟩⟩
  · intro x hx
    refine ⟨?_,?_,?_⟩
    · intro y hy
      obtain ⟨z,hz,_⟩ := ZF.ordinalAddition_existsUnique hZF I x (ord y hy)
      exact ⟨z,ZF.ordinalAddition_mem_omega hZF I hw hx hy hz,(hg x y z).mpr ⟨hx,hy,hz⟩⟩
    · intro y a b hy ha hb
      exact addition_unique hM hw hy ((hg x y a).mp ha).2.2 ((hg x y b).mp hb).2.2
    · intro a b z ha hb hxa hxb
      exact ZF.ordinalAddition_right_injective hZF I (ord x hx) (ord a ha) (ord b hb)
        ((hg x a z).mp hxa).2.2 ((hg x b z).mp hxb).2.2
  · intro a b c ab bc z ha hb hc hab hbc
    have hab' := ((hg a b ab).mp hab).2.2
    have hbc' := ((hg b c bc).mp hbc).2.2
    constructor
    · intro hz
      obtain ⟨s,hs,_⟩ := ZF.ordinalAddition_existsUnique hZF I a (ord bc (closed hbc))
      have he := ZF.ordinalAddition_assoc hZF I (ord a ha) (ord b hb) (ord c hc) hab' hbc' hs
        ((hg ab c z).mp hz).2.2
      exact (hg a bc z).mpr ⟨ha,closed hbc,he ▸ hs⟩
    · intro hz
      obtain ⟨s,hs,_⟩ := ZF.ordinalAddition_existsUnique hZF I ab (ord c hc)
      have he := ZF.ordinalAddition_assoc hZF I (ord a ha) (ord b hb) (ord c hc) hab' hbc'
        ((hg a bc z).mp hz).2.2 hs
      exact (hg ab c z).mpr ⟨closed hab,hc,he.symm ▸ hs⟩

theorem conical (hM : FirstOrder.Theory.Models M nativeZF)
    {w mul zero : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hg : AdditionGraph hM w mul) (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) :
    Conical w mul zero := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  intro x y hx hy h
  have hs := ((hg x y zero).mp h).2.2
  constructor
  · exact (ZF.ordinalAddition_left_eq_or_mem hZF I (hw.members_areOrdinals hZF y hy) hs).resolve_right (hz x)
  · exact (ZF.ordinalAddition_right_eq_or_mem hZF I (hw.members_areOrdinals hZF x hx)
      (hw.members_areOrdinals hZF y hy) hs).resolve_right (hz y)

/-- The source left-divisibility order, distinct from the order on diagrams. -/
def Divides (w mul x y : M.Carrier .set) : Prop :=
  ∃ z, (Project.FirstOrderSemantics.reduct M).mem z w ∧ Product mul x z y

def divides {m : Nat} (w mul x y : Fin m) : Source.Formula m :=
  .ex ((Source.Formula.mem (Fin.last m) w.castSucc).conj
    (ForcingDiagramOrder.product mul.castSucc x.castSucc (Fin.last m) y.castSucc))

theorem divides_semantics {m : Nat} (env : Fin m → M.Carrier .set) (w mul x y : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (divides w mul x y) ↔
      Divides (env w) (env mul) (env x) (env y) := by
  simp only [divides,Divides,Source.Formula.Realize,ForcingDiagramOrder.product_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Literal Base.le_iff: internal natural addition gives the usual ordinal order. -/
theorem le_iff (hM : FirstOrder.Theory.Models M nativeZF) {w mul x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hg : AdditionGraph hM w mul)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x w)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y w) :
    Divides w mul x y ↔ x = y ∨ (Project.FirstOrderSemantics.reduct M).mem x y := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  constructor
  · rintro ⟨z,hz,hprod⟩
    exact ZF.ordinalAddition_left_eq_or_mem hZF I (ord z hz) ((hg x z y).mp hprod).2.2
  · intro h
    rcases h with he | hxy
    · subst y
      obtain ⟨zero,hz,hzw⟩ := hw.1.1
      exact ⟨zero,hzw,(hg x zero x).mpr ⟨hx,hzw,(ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩⟩
    · obtain ⟨z,hz,_⟩ := ZF.ordinalAddition_existsUnique_rightRemainder hZF I (ord x hx) (ord y hy) hxy
      have hzw : (Project.FirstOrderSemantics.reduct M).mem z w := by
        rcases ZF.ordinalAddition_right_eq_or_mem hZF I (ord x hx) hz.right_isOrdinal hz with he | hzy
        · exact he ▸ hy
        · exact hw.transitive hZF y hy z hzy
      exact ⟨z,hzw,(hg x z y).mpr ⟨hx,hzw,hz⟩⟩

/-- Pair least upper bounds; the base has these even without a given upper bound. -/
def Joins (w mul : M.Carrier .set) : Prop :=
  ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x w →
    (Project.FirstOrderSemantics.reduct M).mem y w → ∃ j,
      (Project.FirstOrderSemantics.reduct M).mem j w ∧ ∀ z,
        (Project.FirstOrderSemantics.reduct M).mem z w →
          ((Divides w mul x z ∧ Divides w mul y z) ↔ Divides w mul j z)

theorem joins (hM : FirstOrder.Theory.Models M nativeZF) {w mul : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hg : AdditionGraph hM w mul) : Joins w mul := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  intro x y hx hy
  have cases_order : (x = y ∨ (Project.FirstOrderSemantics.reduct M).mem x y) ∨
      (y = x ∨ (Project.FirstOrderSemantics.reduct M).mem y x) := by
    rcases SetTheory.Structure.IsOrdinal.trichotomy hZF.1 (ord x hx) (ord y hy)
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) x y) with he | hxy | hyx
    · exact Or.inl (Or.inl (hZF.1.eq_of_same_members x y he))
    · exact Or.inl (Or.inr hxy)
    · exact Or.inr (Or.inr hyx)
  rcases cases_order with hxy | hyx
  · refine ⟨y,hy,fun z hz => ?_⟩
    rw [le_iff hM hw hg hx hz,le_iff hM hw hg hy hz]
    exact ⟨And.right,fun hyz => ⟨ZF.eqOrMem_trans (ord z hz) hxy hyz,hyz⟩⟩
  · refine ⟨x,hx,fun z hz => ?_⟩
    rw [le_iff hM hw hg hx hz,le_iff hM hw hg hy hz]
    exact ⟨And.left,fun hxz => ⟨hxz,ZF.eqOrMem_trans (ord z hz) hyx hxz⟩⟩

def joinsFormula {m : Nat} (w mul : Fin m) : Source.Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let x := (Fin.last m).castSucc.castSucc.castSucc
  let y := (Fin.last (m+1)).castSucc.castSucc
  let j := (Fin.last (m+2)).castSucc
  let z := Fin.last (m+3)
  .all (.all ((Source.Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).imp
    ((Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).imp
      (.ex ((Source.Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
        (.all ((Source.Formula.mem z (up w)).imp
          (((divides (up w) (up mul) x z).conj (divides (up w) (up mul) y z)).iff
            (divides (up w) (up mul) j z)))))))))

theorem joinsFormula_semantics {m : Nat} (env : Fin m → M.Carrier .set) (w mul : Fin m) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (joinsFormula w mul) ↔
      Joins (env w) (env mul) := by
  simp only [joinsFormula,Joins,Source.Formula.Realize,Source.Formula.iff,divides_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x y hx hy => by
    obtain ⟨j,hj,h⟩ := h x y hx hy
    exact ⟨j,hj,fun z hz => ⟨(h z hz).1,(h z hz).2⟩⟩,
    fun h x y hx hy => by
    obtain ⟨j,hj,h⟩ := h x y hx hy
    exact ⟨j,hj,fun z hz => ⟨(h z hz).mp,(h z hz).mpr⟩⟩⟩

/-- Exact internal encoding of the source base multiplication table. -/
def graph {m : Nat} (w mul : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.iff
    (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ (2 : Fin (m+3)) 1 0))
    (.conj (.mem (.bound 2) (.bound w.succ.succ.succ))
      (.conj (.mem (.bound 1) (.bound w.succ.succ.succ))
        (Project.Formula.isOrdinalAddition PureKuratowskiProject.convention (.bound 0) (.bound 2) (.bound 1)))))))

theorem graph_freeClosed {m : Nat} (w mul : Fin m) : (graph w mul).FreeClosed := by
  simp -implicitDefEqProofs [graph, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul : Fin m) :
    Project.Formula.satisfies env (graph w mul) ↔ AdditionGraph hM (env.bound w) (env.bound mul) := by
  simp only [graph, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M), Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_isOrdinalAddition_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM), Project.Term.eval_bound]
  rfl

theorem exists_base (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul zero one, AdditionGraph hM w mul ∧
      (∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf one zero ∧
      LeftCancelMonoid w mul zero ∧ Conical w mul zero ∧
      (Project.FirstOrderSemantics.reduct M).mem one w ∧ one ≠ zero ∧ Joins w mul := by
  obtain ⟨mul,hg⟩ := exists_additionGraph hM hw
  obtain ⟨zero,hz,hzw⟩ := hw.1.1
  obtain ⟨one,hone,how⟩ := hw.1.2 zero hzw
  refine ⟨mul,zero,one,hg,hz,hone,leftCancelMonoid hM hw hg hz hzw,conical hM hw hg hz,how,?_,joins hM hw hg⟩
  intro he
  have hm := (hone zero).mpr (Or.inr (fun _ => Iff.rfl))
  exact hz zero (he ▸ hm)

/-- Bound variables after the witnesses: one, zero, multiplication, omega. -/
def algebraBody : Source.Formula 4 :=
  (ForcingDiagramPoset.leftCancelMonoid 3 2 1).conj
    ((ForcingDiagramPoset.conical 3 2 1).conj ((Source.Formula.mem 0 3).conj ((Source.Formula.neg (.equal 0 1)).conj (joinsFormula 3 2))))

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1 (.imp (Project.Formula.isOmega (.bound 0))
    (.existsE (.existsE (.existsE (.conj (graph (3 : Fin 4) 2)
      (.conj (Project.Formula.isEmpty (.bound 1))
        (.conj (Project.Formula.isSuccessor (.bound 0) (.bound 1)) (ProjectSyntax.encode id algebraBody))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,graph_freeClosed,ProjectSyntax.freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound]
  intro hw
  obtain ⟨mul,zero,one,hg,hz,hone,hm,hc,how,hne,hj⟩ := exists_base hM hw
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    graph_semantics hM, Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), algebraBody,
    Source.Formula.Realize,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),joinsFormula_semantics (M := M)]
  exact ⟨mul,zero,one,hg,hz,hone,hm,hc,how,hne,hj⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionBaseMonoid
