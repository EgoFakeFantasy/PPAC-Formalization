/- Pinned BlockIndex.cut_bot/inner_limit/outer_limit and flatten continuity.
Use actual dependent-index data and its already proved Cover facts. Native
ordinal classification supplies limit cases; actual range continuity supplies
strictly earlier cuts. No new order, recursion, limit object or proof kernel. -/
import PPAC.Migration.ConstructionBlockCuts
import PPAC.Migration.ConstructionBlockContinuity

namespace PPAC.Migration.ConstructionCutLimits
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBlockCuts (Cut AllSuccessors)
open ConstructionBlockIndex (Data)
open ConstructionFirstAppearance (Cover At)
open ForcingWithTopCarrier (Empty)
open ForcingConditionGraphs (function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Bottom (zero I R bottom : M.Carrier .set) : Prop :=
  Cut zero zero bottom ∧ (Project.FirstOrderSemantics.reduct M).mem bottom I ∧
    ∀ c, (Project.FirstOrderSemantics.reduct M).mem c I → bottom = c ∨ PureKuratowski.PairMember M bottom c R

def LimitCut (I R bottom c : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem c I ∧ c ≠ bottom ∧ ¬ ∃ b, Cover I R b c

def Cases (kappa Indices zero c : M.Carrier .set) : Prop :=
  Empty (M := M) c ∨ ∃ i J j,
    (Project.FirstOrderSemantics.reduct M).mem i kappa ∧ PureKuratowski.PairMember M i J Indices ∧
    (Project.FirstOrderSemantics.reduct M).mem j J ∧ Cut i j c ∧
    ((Project.FirstOrderSemantics.reduct M).IsLimitOrdinal j ∨
      j = zero ∧ (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal i)

theorem ordinal_limit (hM : FirstOrder.Theory.Models M nativeZF)
    {a zero : M.Carrier .set} (ha : (Project.FirstOrderSemantics.reduct M).IsOrdinal a)
    (hz : Empty (M := M) zero) (hne : a ≠ zero)
    (hno : ¬ ∃ b, (Project.FirstOrderSemantics.reduct M).SuccessorOf a b) :
    (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal a := by
  rcases ha.classify (ModelTransfer.extensionality hM) with he | ⟨b,_,hs⟩ | hl
  · exact (hne (ForcingWithTopCarrier.empty_unique hM he hz)).elim
  · exact (hno ⟨b,hs⟩).elim
  · exact hl

/-- The literal initial cut and its leastness in the SAME actual index. -/
theorem exists_bottom (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R zero : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hd : Data hM kappa traces Indices A r I R)
    (hall : AllSuccessors kappa traces Indices I R zero)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i kappa) :
    ∃ bottom, Bottom zero I R bottom := by
  obtain ⟨i,hi⟩ := hne
  obtain ⟨_,_,_,_,_,hz,_,_,_⟩ := hall i hi
  have hkp := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  have hzK := Structure.IsOrdinal.empty_mem_of_nonempty hkp hk ⟨i,hi⟩ hz
  obtain ⟨J,last,_,hJ,_,_,hzJ,_,_⟩ := hall zero hzK
  obtain ⟨bottom,hbI,hb⟩ := ConstructionBlockCuts.exists_cut hM hd hJ hzJ
  refine ⟨bottom,hb,hbI,?_⟩
  intro c hcI
  have hdCopy := hd
  obtain ⟨_,_,hA,_,_,hI,_,hR⟩ := hdCopy
  rcases (hI c).mp hcI with he | ⟨p,hp,hsc⟩
  · obtain ⟨q,_,hsb⟩ := hb
    exact Or.inr ((hR bottom c).mpr ⟨hbI,hcI,Or.inl ⟨ForcingWithTopCarrier.single_nonempty hsb,he⟩⟩)
  · obtain ⟨k,L,l,hkK,hL,hl,hcode⟩ := (hA p).mp hp
    have hc : Cut k l c := ⟨p,hcode,hsc⟩
    classical
    by_cases ek : k = zero
    · subst k
      by_cases el : l = zero
      · subst l
        exact Or.inl (ConstructionBlockCuts.cut_unique hM hb hc)
      · have hzl := Structure.IsOrdinal.empty_mem_of_nonempty hkp ((hd.2.1.2 zero L hL).mem hl)
          (ConstructionTowerIterationCases.nonzero_nonempty hM hz el) hz
        exact Or.inr ((ConstructionBlockCuts.cut_lt hM hd hb hc hbI hcI).mpr (Or.inr ⟨rfl,hzl⟩))
    · have hzk := Structure.IsOrdinal.empty_mem_of_nonempty hkp (hk.mem hkK)
        (ConstructionTowerIterationCases.nonzero_nonempty hM hz ek) hz
      exact Or.inr ((ConstructionBlockCuts.cut_lt hM hd hb hc hbI hcI).mpr (Or.inl hzk))

theorem inner_limit (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R zero i J j c : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hd : Data hM kappa traces Indices A r I R)
    (hall : AllSuccessors kappa traces Indices I R zero)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) (hc : Cut i j c)
    (hne : j ≠ zero) (hno : ¬ ∃ b, Cover I R b c) :
    (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal j := by
  obtain ⟨_,_,_,_,_,hz,_,_,_⟩ := hall i (function_input hd.2.1.1 hJ)
  exact ordinal_limit hM ((hd.2.1.2 i J hJ).mem hj) hz hne
    (ConstructionBlockCuts.inner_no_predecessor hM hk hd hJ hj hc hno)

theorem outer_limit (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices I R zero i c bottom : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hall : AllSuccessors kappa traces Indices I R zero)
    (hb : Bottom zero I R bottom)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa) (hc : Cut i zero c)
    (hl : LimitCut I R bottom c) :
    (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal i := by
  obtain ⟨_,_,_,_,_,hz,_,_,_⟩ := hall i hi
  have hne : i ≠ zero := by
    intro he
    subst i
    exact hl.2.1 (ConstructionBlockCuts.cut_unique hM hc hb.1)
  exact ordinal_limit hM (hk.mem hi) hz hne
    (ConstructionBlockCuts.outer_no_predecessor hM hk hall hi hc hl.2.2)

/-- Every noninitial predecessor-free index is the final top, an inner
limit, or a zero-position cut at an outer limit. -/
theorem classify (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R zero bottom c : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hd : Data hM kappa traces Indices A r I R)
    (hall : AllSuccessors kappa traces Indices I R zero)
    (hb : Bottom zero I R bottom) (hl : LimitCut I R bottom c) : Cases kappa Indices zero c := by
  have hdCopy := hd
  obtain ⟨_,_,hA,_,_,hI,_,_⟩ := hdCopy
  rcases (hI c).mp hl.1 with he | ⟨p,hp,hsc⟩
  · exact Or.inl he
  · obtain ⟨i,J,j,hi,hJ,hj,hcode⟩ := (hA p).mp hp
    have hc : Cut i j c := ⟨p,hcode,hsc⟩
    refine Or.inr ⟨i,J,j,hi,hJ,hj,hc,?_⟩
    classical
    by_cases he : j = zero
    · subst j
      exact Or.inr ⟨rfl,outer_limit hM hk hall hb hi hc hl⟩
    · exact Or.inl (inner_limit hM hk hd hall hJ hj hc he hl.2.2)

/-- Construct the bottom and full classifier from the actual Family. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top zero one K mu history F kappa traces Indices A r I R : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hf : ConstructionBlockTraces.Family hM w Q values top zero one K mu history F kappa traces)
    (hd : Data hM kappa traces Indices A r I R)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i kappa) :
    ∃ bottom, Bottom zero I R bottom ∧ AllSuccessors kappa traces Indices I R zero ∧
      ∀ c, LimitCut I R bottom c → Cases kappa Indices zero c := by
  have hall := ConstructionBlockCuts.all_successors hM hk hf hd
  obtain ⟨bottom,hb⟩ := exists_bottom hM hk hd hall hne
  exact ⟨bottom,hb,hall,fun _ hl => classify hM hk hd hall hb hl⟩

/-- Consume the actual trace continuity, retaining a strictly earlier cut. -/
theorem inner_range_earlier (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V
      J Domains E F L Out Images kappa traces Indices A r I R i j c x : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hd : Data hM kappa traces Indices A r I R)
    (hall : AllSuccessors kappa traces Indices I R zero)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) (hc : Cut i j c)
    (hne : j ≠ zero) (hno : ¬ ∃ b, Cover I R b c)
    (ht : ConstructionBlockTraces.Trace hM w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code)
    (hb : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images)
    (hx : At Images j x) :
    ∃ k b, (Project.FirstOrderSemantics.reduct M).mem k j ∧ Cut i k b ∧
      PureKuratowski.PairMember M b c R ∧ At Images k x := by
  have hlimit := inner_limit hM hk hd hall hJ hj hc hne hno
  obtain ⟨k,hkj,hkx⟩ := ConstructionBlockContinuity.trace_continuous hM ht hb j hj hlimit x hx
  have hkJ := (hd.2.1.2 i J hJ).transitive j hj k hkj
  obtain ⟨b,hbI,hbCut⟩ := ConstructionBlockCuts.exists_cut hM hd hJ hkJ
  have hcI := (ConstructionBlockCuts.cut_mem hM hd hc).mpr ⟨J,function_input hd.2.1.1 hJ,hJ,hj⟩
  exact ⟨k,b,hkj,hbCut,(ConstructionBlockCuts.cut_lt hM hd hbCut hc hbI hcI).mpr (Or.inr ⟨rfl,hkj⟩),hkx⟩

/-- Initial-position cuts use the already constructed actual outer ranges. -/
theorem outer_range_earlier (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hd : Data hM kappa traces Indices A r I R)
    (hall : AllSuccessors kappa traces Indices I R zero)
    (hb : Bottom zero I R bottom)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa) (hc : Cut i zero c)
    (hl : LimitCut I R bottom c)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (ho : ConstructionBlockContinuity.OuterData B history F terminalLegs V Domains E Images)
    (hx : At Images i x) :
    ∃ k J b, (Project.FirstOrderSemantics.reduct M).mem k i ∧
      PureKuratowski.PairMember M k J Indices ∧ Cut k zero b ∧ PureKuratowski.PairMember M b c R ∧ At Images k x := by
  have hlimit := outer_limit hM hk hall hb hi hc hl
  have hiB := (hB i).mpr (Or.inl hi)
  obtain ⟨k,hki,hkx⟩ := ho.2.2.2.2.2.2.2 i hiB hlimit x hx
  have hkK := hk.transitive i hi k hki
  obtain ⟨J,last,_,hJ,_,_,hzJ,_,_⟩ := hall k hkK
  obtain ⟨b,hbI,hbCut⟩ := ConstructionBlockCuts.exists_cut hM hd hJ hzJ
  exact ⟨k,J,b,hki,hJ,hbCut,(ConstructionBlockCuts.cut_lt hM hd hbCut hc hbI hl.1).mpr (Or.inl hki),hkx⟩

def bottomFormula {m : Nat} (zero I R bottom : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionBlockCuts.cut zero zero bottom) (.conj (.mem (.bound bottom) (.bound I)) (.forallE (.imp
  (.mem (.bound 0) (.bound I.succ)) (.disj (Project.Formula.extensionalEq (.bound bottom.succ) (.bound 0))
  (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ bottom.succ 0)))))))

theorem bottomFormula_freeClosed {m : Nat} (zero I R bottom : Fin m) :
    (bottomFormula zero I R bottom).FreeClosed := by
  simp -implicitDefEqProofs [bottomFormula,Definitional.Formula.FreeClosed,ConstructionBlockCuts.cut_freeClosed,Project.Formula.extensionalEq,ProjectSyntax.freeClosed]

theorem bottomFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero I R bottom : Fin m) :
    Project.Formula.satisfies env (bottomFormula zero I R bottom) ↔ Bottom (env.bound zero) (env.bound I) (env.bound R) (env.bound bottom) := by
  simp only [bottomFormula,Bottom,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBlockCuts.cut_semantics hM]
  rfl

def limitCut {m : Nat} (I R bottom c : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound c) (.bound I)) (.conj (.neg (Project.Formula.extensionalEq (.bound c) (.bound bottom)))
  (.neg (.existsE (ConstructionFirstAppearance.cover I.succ R.succ 0 c.succ)))))

theorem limitCut_freeClosed {m : Nat} (I R bottom c : Fin m) :
    (limitCut I R bottom c).FreeClosed := by
  simp -implicitDefEqProofs [limitCut,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ConstructionFirstAppearance.cover_freeClosed]

theorem limitCut_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I R bottom c : Fin m) :
    Project.Formula.satisfies env (limitCut I R bottom c) ↔ LimitCut (env.bound I) (env.bound R) (env.bound bottom) (env.bound c) := by
  simp only [limitCut,LimitCut,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionFirstAppearance.cover_semantics hM]
  rfl

def cases {m : Nat} (kappa Indices zero c : Fin m) : Project.Formula 1 m :=
  (.disj (ProjectSyntax.encode id (ForcingWithTopCarrier.empty c)) (.existsE (.existsE (.existsE (.conj (.mem
  (.bound 2) (.bound kappa.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Indices.succ.succ.succ 2 1)) (.conj (.mem (.bound 0) (.bound 1)) (.conj (ConstructionBlockCuts.cut 2 0
  c.succ.succ.succ) (.disj (Project.Formula.isLimitOrdinal (.bound 0)) (.conj (Project.Formula.extensionalEq
  (.bound 0) (.bound zero.succ.succ.succ)) (Project.Formula.isLimitOrdinal (.bound 2))))))))))))

theorem cases_freeClosed {m : Nat} (kappa Indices zero c : Fin m) :
    (cases kappa Indices zero c).FreeClosed := by
  simp -implicitDefEqProofs [cases,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionBlockCuts.cut_freeClosed,Project.Formula.extensionalEq,Project.Formula.isLimitOrdinal]

theorem cases_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa Indices zero c : Fin m) :
    Project.Formula.satisfies env (cases kappa Indices zero c) ↔ Cases (env.bound kappa) (env.bound Indices) (env.bound zero) (env.bound c) := by
  simp only [cases,Cases,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingWithTopCarrier.empty_semantics (M := M),ConstructionBlockCuts.cut_semantics hM,Project.Formula.satisfies_isLimitOrdinal_iff]
  rfl

def constructionSentence {m : Nat} (w Q values top zero one K mu history F kappa traces Indices A r I R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (ConstructionBlockTraces.family w Q values top zero
    one K mu history F kappa traces) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp
    (.existsE (.mem (.bound 0) (.bound kappa.succ))) (.existsE (.conj (bottomFormula zero.succ I.succ R.succ 0)
    (.conj (ConstructionBlockCuts.allSuccessors kappa.succ traces.succ Indices.succ I.succ R.succ zero.succ)
    (.forallE (.imp (limitCut I.succ.succ R.succ.succ 1 0) (cases kappa.succ.succ Indices.succ.succ
    zero.succ.succ 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,bottomFormula_freeClosed,ConstructionBlockCuts.allSuccessors_freeClosed,limitCut_freeClosed,cases_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q values top zero one K mu history F kappa traces Indices A r I R : Fin m) : (Project.fo_sentence (constructionSentence w Q values top zero one K mu history F kappa traces Indices A r I R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top zero one K mu history F kappa traces Indices A r I R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,bottomFormula_semantics hM,ConstructionBlockCuts.allSuccessors_semantics hM,limitCut_semantics hM,cases_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w Q values top zero one K mu history F kappa traces Indices A r I R : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (constructionSentence w Q values top zero one K mu history F kappa traces Indices A r I R)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM w Q values top zero one K mu history F kappa traces Indices A r I R

def innerSentence {m : Nat} (w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (ConstructionBlockIndex.data kappa traces Indices A
    r I R) (.imp (ConstructionBlockCuts.allSuccessors kappa traces Indices I R zero) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge Indices i J)) (.imp (.mem (.bound j) (.bound J)) (.imp
    (ConstructionBlockCuts.cut i j c) (.imp (.neg (Project.Formula.extensionalEq (.bound j) (.bound zero)))
    (.imp (.neg (.existsE (ConstructionFirstAppearance.cover I.succ R.succ 0 c.succ))) (.imp
    (ConstructionBlockTraces.trace w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW
    CW O code) (.imp (ConstructionActualBlocks.data code W after V J Domains E F L Out Images) (.imp
    (ConstructionFirstAppearance.atStage Images j x) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound
    j.succ.succ)) (.conj (ConstructionBlockCuts.cut i.succ.succ 1 0) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge R.succ.succ 0 c.succ.succ)) (ConstructionFirstAppearance.atStage Images.succ.succ
    1 x.succ.succ)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionBlockIndex.data_freeClosed,ConstructionBlockCuts.allSuccessors_freeClosed,ProjectSyntax.freeClosed,ConstructionBlockCuts.cut_freeClosed,Project.Formula.extensionalEq,ConstructionFirstAppearance.cover_freeClosed,ConstructionBlockTraces.trace_freeClosed,ConstructionActualBlocks.data_freeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem inner_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x : Fin m) : (Project.fo_sentence (innerSentence w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (innerSentence w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isOrdinal_iff,ConstructionBlockIndex.data_semantics hM,ConstructionBlockCuts.allSuccessors_semantics hM,ConstructionBlockCuts.cut_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionBlockTraces.trace_semantics hM,ConstructionActualBlocks.data_semantics hM,ConstructionFirstAppearance.atStage_semantics hM]
  exact inner_range_earlier hM

theorem inner_kernel_certificate {m : Nat} (w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (innerSentence w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x)) := by
  apply ModelTransfer.derives
  intro M hM
  exact inner_models hM w Q values top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after V J Domains E F L Out Images kappa traces Indices A r I R i j c x

def outerSentence {m : Nat} (kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (ConstructionBlockIndex.data kappa traces Indices A
    r I R) (.imp (ConstructionBlockCuts.allSuccessors kappa traces Indices I R zero) (.imp (bottomFormula zero I R
    bottom) (.imp (.mem (.bound i) (.bound kappa)) (.imp (ConstructionBlockCuts.cut i zero c) (.imp (limitCut
    I R bottom c) (.imp (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.imp
    (ConstructionBlockContinuity.outerData B history F terminalLegs V Domains E Images) (.imp
    (ConstructionFirstAppearance.atStage Images i x) (.existsE (.existsE (.existsE (.conj (.mem (.bound 2)
    (.bound i.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Indices.succ.succ.succ
    2 1)) (.conj (ConstructionBlockCuts.cut 2 zero.succ.succ.succ 0) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge R.succ.succ.succ 0 c.succ.succ.succ)) (ConstructionFirstAppearance.atStage
    Images.succ.succ.succ 2 x.succ.succ.succ))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionBlockIndex.data_freeClosed,ConstructionBlockCuts.allSuccessors_freeClosed,bottomFormula_freeClosed,ConstructionBlockCuts.cut_freeClosed,limitCut_freeClosed,Project.Formula.isSuccessor,ConstructionBlockContinuity.outerData_freeClosed,ConstructionFirstAppearance.atStage_freeClosed,ProjectSyntax.freeClosed]

theorem outer_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x : Fin m) : (Project.fo_sentence (outerSentence kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (outerSentence kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isOrdinal_iff,ConstructionBlockIndex.data_semantics hM,ConstructionBlockCuts.allSuccessors_semantics hM,bottomFormula_semantics hM,ConstructionBlockCuts.cut_semantics hM,limitCut_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionBlockContinuity.outerData_semantics hM,ConstructionFirstAppearance.atStage_semantics hM]
  exact outer_range_earlier hM

theorem outer_kernel_certificate {m : Nat} (kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (outerSentence kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x)) := by
  apply ModelTransfer.derives
  intro M hM
  exact outer_models hM kappa traces Indices A r I R zero bottom i c B history F terminalLegs V Domains E Images x

end PPAC.Migration.ConstructionCutLimits
