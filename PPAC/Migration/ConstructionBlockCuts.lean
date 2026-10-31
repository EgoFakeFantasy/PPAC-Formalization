/- Pinned BlockTowers.BlockIndex.cut/succ_inner/succ_boundary.
Use the SAME actual block index and original internal Cover predicate.
Actual last/zero endpoints are read from the retained complete-round trace. -/
import PPAC.Migration.ConstructionBlockIndex
import PPAC.Migration.ConstructionFirstAppearance

namespace PPAC.Migration.ConstructionBlockCuts
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionBlockIndex (Data)
open ConstructionTowerHistory (Row)
open ConstructionFirstAppearance (Cover)
open ForcingWithTopCarrier (Single Empty)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Cut (i j c : M.Carrier .set) : Prop :=
  ∃ p, PureKuratowski.Code M p i j ∧ Single c p

theorem cut_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {i j c d : M.Carrier .set} (hc : Cut i j c) (hd : Cut i j d) : c = d := by
  obtain ⟨p,hp,hc⟩ := hc
  obtain ⟨q,hq,hd⟩ := hd
  have eq := KuratowskiZF.code_unique hM hp hq
  subst q
  exact ForcingWithTopCarrier.single_unique hM hc hd

theorem cut_mem (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i j c : M.Carrier .set}
    (hD : Data hM kappa traces Indices A r I R) (hc : Cut i j c) :
    (Project.FirstOrderSemantics.reduct M).mem c I ↔
      ∃ J, (Project.FirstOrderSemantics.reduct M).mem i kappa ∧
        PureKuratowski.PairMember M i J Indices ∧ (Project.FirstOrderSemantics.reduct M).mem j J := by
  obtain ⟨_,_,hA,_,_,hI,_,_⟩ := hD
  obtain ⟨p,hpc,hsc⟩ := hc
  constructor
  · intro hc
    rcases (hI c).mp hc with he | ⟨q,hq,hqs⟩
    · exact (ForcingWithTopCarrier.single_nonempty hsc he).elim
    · have epq := ForcingWithTopCarrier.single_injective hsc hqs
      subst q
      obtain ⟨i',J,j',hi,hJ,hj,hp⟩ := (hA p).mp hq
      obtain ⟨ei,ej⟩ := PureKuratowski.code_injective hp hpc
      subst i' j'
      exact ⟨J,hi,hJ,hj⟩
  · rintro ⟨J,hi,hJ,hj⟩
    exact (hI c).mpr (Or.inr ⟨p,(hA p).mpr ⟨i,J,j,hi,hJ,hj,hpc⟩,hsc⟩)

theorem exists_cut (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i J j : M.Carrier .set}
    (hD : Data hM kappa traces Indices A r I R)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c I ∧ Cut i j c := by
  obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM i j
  obtain ⟨c,hc⟩ := ForcingWithTopCarrier.exists_single hM p
  have hCut : Cut i j c := ⟨p,hp,hc⟩
  exact ⟨c,(cut_mem hM hD hCut).mpr ⟨J,function_input hD.2.1.1 hJ,hJ,hj⟩,hCut⟩

theorem cut_lt (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i j k l c d : M.Carrier .set}
    (hD : Data hM kappa traces Indices A r I R)
    (hc : Cut i j c) (hd : Cut k l d)
    (hcI : (Project.FirstOrderSemantics.reduct M).mem c I)
    (hdI : (Project.FirstOrderSemantics.reduct M).mem d I) :
    PureKuratowski.PairMember M c d R ↔
      (Project.FirstOrderSemantics.reduct M).mem i k ∨ i = k ∧ (Project.FirstOrderSemantics.reduct M).mem j l := by
  obtain ⟨p,hpc,hsc⟩ := hc
  obtain ⟨q,hqc,hsd⟩ := hd
  have hCopy := hD
  obtain ⟨_,_,hA,_,hG,_,_,hR⟩ := hCopy
  have hpA : (Project.FirstOrderSemantics.reduct M).mem p A := by
    obtain ⟨J,hi,hJ,hj⟩ := (cut_mem hM hD ⟨p,hpc,hsc⟩).mp hcI
    exact (hA p).mpr ⟨i,J,j,hi,hJ,hj,hpc⟩
  have hqA : (Project.FirstOrderSemantics.reduct M).mem q A := by
    obtain ⟨K,hk,hK,hl⟩ := (cut_mem hM hD ⟨q,hqc,hsd⟩).mp hdI
    exact (hA q).mpr ⟨k,K,l,hk,hK,hl,hqc⟩
  constructor
  · intro hcd
    rcases ((hR c d).mp hcd).2.2 with ⟨_,he⟩ | ⟨p',q',hsp,hsq,hpq⟩
    · exact (ForcingWithTopCarrier.single_nonempty hsd he).elim
    · have ep := ForcingWithTopCarrier.single_injective hsc hsp
      have eq := ForcingWithTopCarrier.single_injective hsd hsq
      subst p' q'
      exact (ConstructionBlockIndex.lex_pair hpc hqc).mp ((hG p q).mp hpq).2.2
  · intro h
    exact (hR c d).mpr ⟨hcI,hdI,Or.inr ⟨p,q,hsc,hsd,
      (hG p q).mpr ⟨hpA,hqA,(ConstructionBlockIndex.lex_pair hpc hqc).mpr h⟩⟩⟩

/-- Every strict predecessor is an actual cut; the final top is excluded. -/
theorem source_cut (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R c d : M.Carrier .set}
    (hD : Data hM kappa traces Indices A r I R) (hcd : PureKuratowski.PairMember M c d R) :
    ∃ i J j, (Project.FirstOrderSemantics.reduct M).mem i kappa ∧
      PureKuratowski.PairMember M i J Indices ∧ (Project.FirstOrderSemantics.reduct M).mem j J ∧ Cut i j c := by
  obtain ⟨_,_,hA,_,_,hI,_,hR⟩ := hD
  obtain ⟨hcI,_,hlt⟩ := (hR c d).mp hcd
  have hn : ¬ Empty c := by
    rcases hlt with ⟨hn,_⟩ | ⟨p,_,hs,_,_⟩
    · exact hn
    · exact ForcingWithTopCarrier.single_nonempty hs
  rcases (hI c).mp hcI with he | ⟨p,hp,hs⟩
  · exact (hn he).elim
  · obtain ⟨i,J,j,hi,hJ,hj,hpc⟩ := (hA p).mp hp
    exact ⟨i,J,j,hi,hJ,hj,p,hpc,hs⟩

theorem inner_cover (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i J j next c d : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hD : Data hM kappa traces Indices A r I R)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hn : (Project.FirstOrderSemantics.reduct M).mem next J)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf next j)
    (hc : Cut i j c) (hd : Cut i next d) : Cover I R c d := by
  let N := Project.FirstOrderSemantics.reduct M
  have hi := function_input hD.2.1.1 hJ
  have hJO := hD.2.1.2 i J hJ
  have hj := hJO.transitive next hn j hs.predecessor_mem
  have hcI := (cut_mem hM hD hc).mpr ⟨J,hi,hJ,hj⟩
  have hdI := (cut_mem hM hD hd).mpr ⟨J,hi,hJ,hn⟩
  refine ⟨hcI,hdI,(cut_lt hM hD hc hd hcI hdI).mpr (Or.inr ⟨rfl,hs.predecessor_mem⟩),?_⟩
  intro b hb hcb hbd
  obtain ⟨k,K,l,hk',hK,hl,hbCut⟩ := source_cut hM hD hbd
  have h1 := (cut_lt hM hD hc hbCut hcI hb).mp hcb
  have h2 := (cut_lt hM hD hbCut hd hb hdI).mp hbd
  rcases h1 with hik | ⟨eik,hjl⟩
  · rcases h2 with hki | ⟨eki,_⟩
    · exact hk.wellOrder.linear.irrefl i hi (hk.wellOrder.linear.trans i hi k hk' i hi hik hki)
    · subst k
      exact hk.wellOrder.linear.irrefl i hi hik
  · subst k
    rcases h2 with hii | ⟨_,hln⟩
    · exact hk.wellOrder.linear.irrefl i hi hii
    · have eK := function_unique hD.2.1.1 hK hJ
      subst K
      rcases (hs l).mp hln with hlj | he
      · exact hJO.wellOrder.linear.irrefl j hj (hJO.wellOrder.linear.trans j hj l hl j hj hjl hlj)
      · have elj := (ModelTransfer.extensionality hM).eq_of_same_members l j he
        subst l
        exact hJO.wellOrder.linear.irrefl j hj hjl

theorem boundary_cover (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i next J K last zero c d : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hD : Data hM kappa traces Indices A r I R)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hK : PureKuratowski.PairMember M next K Indices)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf next i)
    (hLast : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last)
    (hz : Empty (M := M) zero) (hzK : (Project.FirstOrderSemantics.reduct M).mem zero K)
    (hc : Cut i last c) (hd : Cut next zero d) : Cover I R c d := by
  have hi := function_input hD.2.1.1 hJ
  have hn := function_input hD.2.1.1 hK
  have hJO := hD.2.1.2 i J hJ
  have hl := hLast.predecessor_mem
  have hcI := (cut_mem hM hD hc).mpr ⟨J,hi,hJ,hl⟩
  have hdI := (cut_mem hM hD hd).mpr ⟨K,hn,hK,hzK⟩
  refine ⟨hcI,hdI,(cut_lt hM hD hc hd hcI hdI).mpr (Or.inl hs.predecessor_mem),?_⟩
  intro b hb hcb hbd
  obtain ⟨k,L,l,hk',hL,hll,hbCut⟩ := source_cut hM hD hbd
  have h1 := (cut_lt hM hD hc hbCut hcI hb).mp hcb
  have h2 := (cut_lt hM hD hbCut hd hb hdI).mp hbd
  rcases h1 with hik | ⟨eik,hlastl⟩
  · rcases h2 with hkn | ⟨_,hlz⟩
    · rcases (hs k).mp hkn with hki | he
      · exact hk.wellOrder.linear.irrefl i hi (hk.wellOrder.linear.trans i hi k hk' i hi hik hki)
      · have eki := (ModelTransfer.extensionality hM).eq_of_same_members k i he
        subst k
        exact hk.wellOrder.linear.irrefl i hi hik
    · exact hz l hlz
  · subst k
    have eL := function_unique hD.2.1.1 hL hJ
    subst L
    rcases (hLast l).mp hll with hllast | he
    · exact hJO.wellOrder.linear.irrefl last hl (hJO.wellOrder.linear.trans last hl l hll last hl hlastl hllast)
    · have el := (ModelTransfer.extensionality hM).eq_of_same_members l last he
      subst l
      exact hJO.wellOrder.linear.irrefl last hl hlastl

def Ends (traces i J last : M.Carrier .set) : Prop :=
  ∃ Schedule inner Finner Steps Events Roots L,
    Row traces i J Schedule last inner Finner Steps Events Roots L

theorem actual_ends (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F kappa traces i : M.Carrier .set}
    (hf : ConstructionBlockTraces.Family hM w Q R top zero one K mu history F kappa traces)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa) :
    ∃ J last, Ends traces i J last ∧ (Project.FirstOrderSemantics.reduct M).IsOrdinal J ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf J last ∧ Empty (M := M) zero ∧
      (Project.FirstOrderSemantics.reduct M).mem zero J := by
  obtain ⟨J,Schedule,last,inner,Finner,Steps,Events,Roots,L,hRow⟩ := ConstructionBlockTraces.family_row hM hf hi
  have hEnds : Ends traces i J last := ⟨Schedule,inner,Finner,Steps,Events,Roots,L,hRow⟩
  obtain ⟨code,hcode,hPack⟩ := hRow
  have hAt := ((hf.2 i code).mp hcode).2.1
  obtain ⟨j,raw,Requests,N,mulN,eN,markN,HN,CN,L0,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    _,_,_,_,_,_,_,_,hTrace⟩ := hAt
  obtain ⟨u,A0,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    inner',P,Finner',Steps',Events',Roots',L',hPack',hCtx,hSchedule,_⟩ := hTrace
  have eqs := ConstructionRoundSelection.pack_injective hPack hPack'
  have eqJ := eqs.1
  have eqLast := eqs.2.2.1
  subst J' last'
  obtain ⟨_,_,_,_,_,_,_,hz,_,hJ,_,_⟩ := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hl,_,_,hs,_⟩ := hSchedule
  have hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last := by
    intro x
    constructor
    · intro hx
      rcases (hs x).mp hx with h | e
      · exact Or.inl h
      · subst x
        exact Or.inr (fun _ => Iff.rfl)
    · rintro (h | e)
      · exact (hs x).mpr (Or.inl h)
      · exact (hs x).mpr (Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members x last e))
  exact ⟨J,last,hEnds,hJ,hSucc,hz,SetTheory.Structure.IsOrdinal.empty_mem_of_nonempty
    (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) hJ ⟨last,hl⟩ hz⟩

theorem ends_index (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i J last : M.Carrier .set}
    (hD : Data hM kappa traces Indices A r I R)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa) (he : Ends traces i J last) :
    PureKuratowski.PairMember M i J Indices := by
  obtain ⟨Schedule,inner,Finner,Steps,Events,Roots,L,hRow⟩ := he
  exact (hD.1.2 i J).mpr ⟨hi,J,Schedule,last,inner,Finner,Steps,Events,Roots,L,hRow,rfl⟩

def Inner (J last I R i : M.Carrier .set) : Prop :=
  ∀ j c, (Project.FirstOrderSemantics.reduct M).mem j last → Cut i j c →
    ∃ next d, (Project.FirstOrderSemantics.reduct M).SuccessorOf next j ∧
      (Project.FirstOrderSemantics.reduct M).mem next J ∧ Cut i next d ∧ Cover I R c d

def Boundary (kappa I R zero i last : M.Carrier .set) : Prop :=
  ∀ next, (Project.FirstOrderSemantics.reduct M).mem next kappa →
    (Project.FirstOrderSemantics.reduct M).SuccessorOf next i →
    ∃ c d, Cut i last c ∧ Cut next zero d ∧ Cover I R c d

def Stage (kappa traces Indices I R zero i J last : M.Carrier .set) : Prop :=
  Ends traces i J last ∧ PureKuratowski.PairMember M i J Indices ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf J last ∧ Empty (M := M) zero ∧
    (Project.FirstOrderSemantics.reduct M).mem zero J ∧ Inner J last I R i ∧ Boundary kappa I R zero i last

def AllSuccessors (kappa traces Indices I R zero : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i kappa →
    ∃ J last, Stage kappa traces Indices I R zero i J last

/-- All source successor cuts, with actual last/bottom witnesses discharged. -/
theorem all_successors (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F kappa traces Indices A r I order : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hf : ConstructionBlockTraces.Family hM w Q R top zero one K mu history F kappa traces)
    (hD : Data hM kappa traces Indices A r I order) :
    AllSuccessors kappa traces Indices I order zero := by
  intro i hi
  obtain ⟨J,last,hEnds,hJ,hSucc,hz,hzJ⟩ := actual_ends hM hf hi
  have hJi := ends_index hM hD hi hEnds
  refine ⟨J,last,hEnds,hJi,hSucc,hz,hzJ,?_,?_⟩
  · intro j c hj hc
    obtain ⟨next,hn,hs,_⟩ := ConstructionCompleteRound.successor_before_last hM hJ hSucc.predecessor_mem hj
    obtain ⟨d,_,hd⟩ := exists_cut hM hD hJi hn
    exact ⟨next,d,hs,hn,hd,inner_cover hM hk hD hJi hn hs hc hd⟩
  · intro next hn hs
    obtain ⟨K,lastK,hEndsK,_,_,_,hzK⟩ := actual_ends hM hf hn
    have hKn := ends_index hM hD hn hEndsK
    obtain ⟨c,_,hc⟩ := exists_cut hM hD hJi hSucc.predecessor_mem
    obtain ⟨d,_,hd⟩ := exists_cut hM hD hKn hzK
    exact ⟨c,d,hc,hd,boundary_cover hM hk hD hJi hKn hs hSucc hz hzK hc hd⟩

/-- The source inner-limit argument: no predecessor cut excludes a successor
inner ordinal, using the SAME cut and Cover relation. -/
theorem inner_no_predecessor (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices A r I R i J j c : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hD : Data hM kappa traces Indices A r I R)
    (hJ : PureKuratowski.PairMember M i J Indices)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) (hc : Cut i j c)
    (hNo : ¬ ∃ b, Cover I R b c) :
    ¬ ∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf j prev := by
  rintro ⟨prev,hs⟩
  have hp := (hD.2.1.2 i J hJ).transitive j hj prev hs.predecessor_mem
  obtain ⟨b,_,hb⟩ := exists_cut hM hD hJ hp
  exact hNo ⟨b,inner_cover hM hk hD hJ hj hs hb hc⟩

/-- The source boundary-limit argument consumes actual preceding endpoints. -/
theorem outer_no_predecessor (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa traces Indices I R zero i c : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hAll : AllSuccessors kappa traces Indices I R zero)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i kappa) (hc : Cut i zero c)
    (hNo : ¬ ∃ b, Cover I R b c) :
    ¬ ∃ prev, (Project.FirstOrderSemantics.reduct M).SuccessorOf i prev := by
  rintro ⟨prev,hs⟩
  have hp := hk.transitive i hi prev hs.predecessor_mem
  obtain ⟨J,last,_,_,_,_,_,_,hBoundary⟩ := hAll prev hp
  obtain ⟨a,b,_,hb,hCover⟩ := hBoundary i hi hs
  have eq := cut_unique hM hb hc
  subst b
  exact hNo ⟨a,hCover⟩

def cut {m : Nat} (i j c : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (PureKuratowskiProject.code (.bound 0) (.bound i.succ) (.bound j.succ)) (ProjectSyntax.encode
  id (ForcingWithTopCarrier.single c.succ 0))))

theorem cut_freeClosed {m : Nat} (i j c : Fin m) :
    (cut i j c).FreeClosed := by
  simp -implicitDefEqProofs [cut,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ProjectSyntax.freeClosed]

theorem cut_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (i j c : Fin m) :
    Project.Formula.satisfies env (cut i j c) ↔
      Cut (env.bound i) (env.bound j) (env.bound c) := by
  simp only [cut,Cut,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingWithTopCarrier.single_semantics (M := M)]
  rfl

def ends {m : Nat} (traces i J last : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (ConstructionTowerHistory.row
  traces.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ
  J.succ.succ.succ.succ.succ.succ.succ 6 last.succ.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0))))))))

theorem ends_freeClosed {m : Nat} (traces i J last : Fin m) :
    (ends traces i J last).FreeClosed := by
  simp -implicitDefEqProofs [ends,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed]

theorem ends_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (traces i J last : Fin m) :
    Project.Formula.satisfies env (ends traces i J last) ↔
      Ends (env.bound traces) (env.bound i) (env.bound J) (env.bound last) := by
  simp only [ends,Ends,Project.Formula.satisfies_exists_iff,ConstructionTowerHistory.row_semantics hM]
  rfl

def inner {m : Nat} (J last I R i : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound last.succ.succ)) (.imp (cut i.succ.succ 1 0) (.existsE
  (.existsE (.conj (Project.Formula.isSuccessor (.bound 1) (.bound 3)) (.conj (.mem (.bound 1) (.bound
  J.succ.succ.succ.succ)) (.conj (cut i.succ.succ.succ.succ 1 0) (ConstructionFirstAppearance.cover
  I.succ.succ.succ.succ R.succ.succ.succ.succ 2 0))))))))))

theorem inner_freeClosed {m : Nat} (J last I R i : Fin m) :
    (inner J last I R i).FreeClosed := by
  simp -implicitDefEqProofs [inner,Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,cut_freeClosed,ConstructionFirstAppearance.cover_freeClosed]

theorem inner_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J last I R i : Fin m) :
    Project.Formula.satisfies env (inner J last I R i) ↔
      Inner (env.bound J) (env.bound last) (env.bound I) (env.bound R) (env.bound i) := by
  simp only [inner,Inner,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,cut_semantics hM,ConstructionFirstAppearance.cover_semantics hM]
  rfl

def boundary {m : Nat} (kappa I R zero i last : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound kappa.succ)) (.imp (Project.Formula.isSuccessor (.bound 0) (.bound
  i.succ)) (.existsE (.existsE (.conj (cut i.succ.succ.succ last.succ.succ.succ 1) (.conj (cut 2
  zero.succ.succ.succ 0) (ConstructionFirstAppearance.cover I.succ.succ.succ R.succ.succ.succ 1 0))))))))

theorem boundary_freeClosed {m : Nat} (kappa I R zero i last : Fin m) :
    (boundary kappa I R zero i last).FreeClosed := by
  simp -implicitDefEqProofs [boundary,Definitional.Formula.FreeClosed,Project.Formula.isSuccessor,cut_freeClosed,ConstructionFirstAppearance.cover_freeClosed]

theorem boundary_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa I R zero i last : Fin m) :
    Project.Formula.satisfies env (boundary kappa I R zero i last) ↔
      Boundary (env.bound kappa) (env.bound I) (env.bound R) (env.bound zero) (env.bound i) (env.bound last) := by
  simp only [boundary,Boundary,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,cut_semantics hM,ConstructionFirstAppearance.cover_semantics hM]
  rfl

def stage {m : Nat} (kappa traces Indices I R zero i J last : Fin m) : Project.Formula 1 m :=
  (.conj (ends traces i J last) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Indices i J)) (.conj
  (Project.Formula.isSuccessor (.bound J) (.bound last)) (.conj (ProjectSyntax.encode id
  (ForcingWithTopCarrier.empty zero)) (.conj (.mem (.bound zero) (.bound J)) (.conj (inner J last I R i)
  (boundary kappa I R zero i last)))))))

theorem stage_freeClosed {m : Nat} (kappa traces Indices I R zero i J last : Fin m) :
    (stage kappa traces Indices I R zero i J last).FreeClosed := by
  simp -implicitDefEqProofs [stage,Definitional.Formula.FreeClosed,ends_freeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,inner_freeClosed,boundary_freeClosed]

theorem stage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa traces Indices I R zero i J last : Fin m) :
    Project.Formula.satisfies env (stage kappa traces Indices I R zero i J last) ↔
      Stage (env.bound kappa) (env.bound traces) (env.bound Indices) (env.bound I) (env.bound R) (env.bound zero) (env.bound i) (env.bound J) (env.bound last) := by
  simp only [stage,Stage,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ends_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingWithTopCarrier.empty_semantics (M := M),inner_semantics hM,boundary_semantics hM]
  rfl

def allSuccessors {m : Nat} (kappa traces Indices I R zero : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound kappa.succ)) (.existsE (.existsE (stage kappa.succ.succ.succ
  traces.succ.succ.succ Indices.succ.succ.succ I.succ.succ.succ R.succ.succ.succ zero.succ.succ.succ 2 1 0)))))

theorem allSuccessors_freeClosed {m : Nat} (kappa traces Indices I R zero : Fin m) :
    (allSuccessors kappa traces Indices I R zero).FreeClosed := by
  simp -implicitDefEqProofs [allSuccessors,Definitional.Formula.FreeClosed,stage_freeClosed]

theorem allSuccessors_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa traces Indices I R zero : Fin m) :
    Project.Formula.satisfies env (allSuccessors kappa traces Indices I R zero) ↔
      AllSuccessors (env.bound kappa) (env.bound traces) (env.bound Indices) (env.bound I) (env.bound R) (env.bound zero) := by
  simp only [allSuccessors,AllSuccessors,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,stage_semantics hM]
  rfl

def constructionSentence {m : Nat} (w Q R top zero one K mu history F kappa traces Indices A r I order : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (ConstructionBlockTraces.family w Q R top zero one K
    mu history F kappa traces) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I order)
    (allSuccessors kappa traces Indices I order zero))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionBlockIndex.data_freeClosed,allSuccessors_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat} (w Q R top zero one K mu history F kappa traces Indices A r I order : Fin m) :
    (Project.fo_sentence (constructionSentence w Q R top zero one K mu history F kappa traces Indices A r I order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w Q R top zero one K mu history F kappa traces Indices A r I order)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,ConstructionBlockTraces.family_semantics hM,ConstructionBlockIndex.data_semantics hM,allSuccessors_semantics hM]
  exact all_successors hM

theorem construction_kernel_certificate {m : Nat} (w Q R top zero one K mu history F kappa traces Indices A r I order : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w Q R top zero one K mu history F kappa traces Indices A r I order)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM w Q R top zero one K mu history F kappa traces Indices A r I order

def innerLimitSentence {m : Nat} (kappa traces Indices A r I R i J j c : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (ConstructionBlockIndex.data kappa traces Indices A r
    I R) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Indices i J)) (.imp (.mem (.bound j) (.bound
    J)) (.imp (cut i j c) (.imp (.neg (.existsE (ConstructionFirstAppearance.cover I.succ R.succ 0 c.succ)))
    (.neg (.existsE (Project.Formula.isSuccessor (.bound j.succ) (.bound 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBlockIndex.data_freeClosed,ProjectSyntax.freeClosed,cut_freeClosed,ConstructionFirstAppearance.cover_freeClosed,Project.Formula.isSuccessor]

theorem innerLimit_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat} (kappa traces Indices A r I R i J j c : Fin m) :
    (Project.fo_sentence (innerLimitSentence kappa traces Indices A r I R i J j c)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (innerLimitSentence kappa traces Indices A r I R i J j c)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isSuccessor_iff,ConstructionBlockIndex.data_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,cut_semantics hM,ConstructionFirstAppearance.cover_semantics hM]
  exact inner_no_predecessor hM

theorem innerLimit_kernel_certificate {m : Nat} (kappa traces Indices A r I R i J j c : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (innerLimitSentence kappa traces Indices A r I R i J j c)) := by
  apply ModelTransfer.derives
  intro M hM
  exact innerLimit_models hM kappa traces Indices A r I R i J j c

def outerLimitSentence {m : Nat} (kappa traces Indices I R zero i c : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (allSuccessors kappa traces Indices I R zero) (.imp
    (.mem (.bound i) (.bound kappa)) (.imp (cut i zero c) (.imp (.neg (.existsE
    (ConstructionFirstAppearance.cover I.succ R.succ 0 c.succ))) (.neg (.existsE (Project.Formula.isSuccessor
    (.bound i.succ) (.bound 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,allSuccessors_freeClosed,cut_freeClosed,ConstructionFirstAppearance.cover_freeClosed,Project.Formula.isSuccessor]

theorem outerLimit_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat} (kappa traces Indices I R zero i c : Fin m) :
    (Project.fo_sentence (outerLimitSentence kappa traces Indices I R zero i c)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (outerLimitSentence kappa traces Indices I R zero i c)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isSuccessor_iff,allSuccessors_semantics hM,cut_semantics hM,ConstructionFirstAppearance.cover_semantics hM]
  exact outer_no_predecessor hM

theorem outerLimit_kernel_certificate {m : Nat} (kappa traces Indices I R zero i c : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (outerLimitSentence kappa traces Indices I R zero i c)) := by
  apply ModelTransfer.derives
  intro M hM
  exact outerLimit_models hM kappa traces Indices I R zero i c

end PPAC.Migration.ConstructionBlockCuts
