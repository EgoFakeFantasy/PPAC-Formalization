/- Pinned ProbeWords.Raw.eval, using the existing native bounded recursion.
   A reversed letter sequence f:n->S is evaluated in a Word-valued history
   of length n+1. No external List or well-foundedness assumption is used. -/
import PPAC.Migration.ConstructionProbeLetterAction

namespace PPAC.Migration.ConstructionProbeEvaluation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeLetterAction (LetterAct letterAct_total letterAct_unique letterAct_word)
open ConstructionProbeAlphabet (Alphabet)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Step (w D S zero mul A b W E f x input H y : M.Carrier .set) : Prop := ∃ k,
  (Project.FirstOrderSemantics.reduct M).mem k w ∧ MapsTo k W H ∧
  (((∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i k) ∧ OldAct w D S zero mul A x input y) ∨
    ∃ j s v, (Project.FirstOrderSemantics.reduct M).SuccessorOf k j ∧
      PureKuratowski.PairMember M j s f ∧ PureKuratowski.PairMember M j v H ∧
        LetterAct w D S zero mul A b W E s v y)

theorem step_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E f x input H y k : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k w) (hH : MapsTo k W H) :
    Step w D S zero mul A b W E f x input H y ↔
      (((∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i k) ∧ OldAct w D S zero mul A x input y) ∨
        ∃ j s v, (Project.FirstOrderSemantics.reduct M).SuccessorOf k j ∧
          PureKuratowski.PairMember M j s f ∧ PureKuratowski.PairMember M j v H ∧
            LetterAct w D S zero mul A b W E s v y) := by
  constructor
  · rintro ⟨k',hk',hH',hy⟩
    have hZF := ModelTransfer.project_models_iff.mp hM
    have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (native_sequence hM (hw.members_areOrdinals hZF k hk) hH)
      (native_sequence hM (hw.members_areOrdinals hZF k' hk') hH')
    subst k'
    exact hy
  · exact fun hy => ⟨k,hk,hH,hy⟩

theorem step_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E f x input H y z e I n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hf : MapsTo n S f)
    (hy : Step w D S zero mul A b W E f x input H y)
    (hzv : Step w D S zero mul A b W E f x input H z) : y = z := by
  obtain ⟨k,hk,hH,hy⟩ := hy
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hkOrd := hw.members_areOrdinals hZF k hk
  have hzv := (step_at hM hw hk hH).mp hzv
  rcases hy with ⟨hempty,hy⟩ | ⟨j,s,v,hkj,hjs,hjv,hy⟩
  · rcases hzv with ⟨_,hzv⟩ | ⟨j,s,v,hkj,_,_,_⟩
    · exact oldAct_unique hM hw hz hm hAlpha.2.1 hy hzv
    · exact (hempty j hkj.predecessor_mem).elim
  · rcases hzv with ⟨hempty,_⟩ | ⟨j',s',v',hkj',hjs',hjv',hzv⟩
    · exact (hempty j hkj.predecessor_mem).elim
    · have he := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1
        (hkOrd.mem hkj.predecessor_mem) hkj hkj'
      subst j'
      have he := ForcingConditionGraphs.function_unique hf.1 hjs hjs'
      subst s'
      have he := ForcingConditionGraphs.function_unique hH.1 hjv hjv'
      subst v'
      exact letterAct_unique hM hw hz hm hAlpha hy hzv

theorem step_word (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E f x input H y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W)
    (hi : (Project.FirstOrderSemantics.reduct M).mem input W)
    (hy : Step w D S zero mul A b W E f x input H y) :
    (Project.FirstOrderSemantics.reduct M).mem y W := by
  obtain ⟨k,_,_,hy⟩ := hy
  rcases hy with ⟨_,hy⟩ | ⟨j,s,v,_,_,_,hy⟩
  · exact (hW y).mpr ((ConstructionProbeReduced.reduced_oldAct hM hw hz hzw hy).mpr ((hW input).mp hi))
  · exact letterAct_word hM hw hz hzw hW hy

theorem step_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E f x input H n m e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hi : (Project.FirstOrderSemantics.reduct M).mem input W)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hmw : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n) (hf : MapsTo n S f)
    (hH : (Project.FirstOrderSemantics.reduct M).IsSequenceInBelow (KuratowskiZF.interpretation hM) H m W) :
    ∃ y, Step w D S zero mul A b W E f x input H y := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨_,k,hkm,hH⟩ := hH
  have hk : (Project.FirstOrderSemantics.reduct M).mem k w := (hw.isOrdinal hZF).transitive m hmw k hkm
  have hMaps : MapsTo k W H := (ForcingSupportSize.native_mapsTo hM k W H).mpr hH.2
  by_cases hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i k
  · obtain ⟨j,hjw,hkj⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hk hne
    have hjn : (Project.FirstOrderSemantics.reduct M).mem j n := by
      rcases (hSucc k).mp hkm with hkn | heq
      · exact (hw.members_areOrdinals hZF n hn).transitive k hkn j hkj.predecessor_mem
      · have he : k = n := (ModelTransfer.extensionality hM).eq_of_same_members k n heq
        exact he ▸ hkj.predecessor_mem
    obtain ⟨s,hjs,_⟩ := hf.1.2 j hjn
    obtain ⟨v,hjv,_⟩ := hMaps.1.2 j hkj.predecessor_mem
    obtain ⟨y,hy⟩ := letterAct_total hM hw hz hzw hm hAlpha hW hb (hf.2 j s hjs) (hMaps.2 j v hjv)
    exact ⟨y,k,hk,hMaps,Or.inr ⟨j,s,v,hkj,hjs,hjv,hy⟩⟩
  · obtain ⟨y,hy⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hx (word_raw hW hi)
    exact ⟨y,k,hk,hMaps,Or.inl ⟨fun i hi => hne ⟨i,hi⟩,hy⟩⟩


def step {m : Nat} (w D S zero mul A b W E f x input H y : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound w.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo H.succ 0 W.succ))
      (.disj (.conj (Project.Formula.isEmpty (.bound 0))
        (ConstructionProbeRawActionSyntax.oldAct w.succ D.succ S.succ zero.succ mul.succ A.succ x.succ input.succ y.succ))
        (.existsE (.existsE (.existsE (.conj
          (Project.Formula.isSuccessor (.bound 3) (.bound 2))
          (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ 2 1))
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ 2 0))
              (ConstructionProbeLetterAction.letterAct w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ b.succ.succ.succ.succ W.succ.succ.succ.succ E.succ.succ.succ.succ 1 0 y.succ.succ.succ.succ))))))))))

theorem step_freeClosed {m : Nat} (w D S zero mul A b W E f x input H y : Fin m) :
    (step w D S zero mul A b W E f x input H y).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.extensionalEq_freeClosed_iff,
    ConstructionProbeRawActionSyntax.oldAct_freeClosed,ConstructionProbeLetterAction.letterAct_freeClosed]

theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D S zero mul A b W E f x input H y : Fin m) :
    Project.Formula.satisfies env (step w D S zero mul A b W E f x input H y) ↔
      Step (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound f) (env.bound x) (env.bound input) (env.bound H) (env.bound y) := by
  simp only [step,Step,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionProbeRawActionSyntax.oldAct_semantics hM,ConstructionProbeLetterAction.letterAct_semantics hM]
  rfl

def stepSchema {m : Nat} (w D S zero mul A b W E f x input : Fin m) : Project.BinarySchema m where
  body := step w.succ.succ D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ b.succ.succ W.succ.succ E.succ.succ f.succ.succ x.succ.succ input.succ.succ 1 0
  freeClosed := step_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem stepSchema_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D S zero mul A b W E f x input : Fin m) (H y : M.Carrier .set) :
    (stepSchema w D S zero mul A b W E f x input).denote env H y ↔
      Step (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound f) (env.bound x) (env.bound input) H y :=
  step_semantics hM ((env.push H).push y) w.succ.succ D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ b.succ.succ W.succ.succ E.succ.succ f.succ.succ x.succ.succ input.succ.succ 1 0

def History (hM : FirstOrder.Theory.Models M nativeZF)
    (w D S zero mul A b W E f x input H m : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsRecursiveSequenceIn (KuratowskiZF.interpretation hM)
    (Step w D S zero mul A b W E f x input) H m W

theorem history_existsUnique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E f x input n m e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hi : (Project.FirstOrderSemantics.reduct M).mem input W)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hmw : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n) (hf : MapsTo n S f) :
    ∃ H, History hM w D S zero mul A b W E f x input H m ∧
      ∀ H', History hM w D S zero mul A b W E f x input H' m → H' = H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 12 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul (Fin.cases A (Fin.cases b (Fin.cases W (Fin.cases E (Fin.cases f (Fin.cases x (fun _ => input)))))))))))
    free := fun _ => w }
  let schema := stepSchema (0 : Fin 12) 1 2 3 4 5 6 7 8 9 10 11
  have he : schema.denote env = Step w D S zero mul A b W E f x input := by
    funext H y
    exact propext (stepSchema_semantics hM env 0 1 2 3 4 5 6 7 8 9 10 11 H y)
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hOperator : (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnSequencesInBelow
      (KuratowskiZF.interpretation hM) (schema.denote env) m W := by
    rw [he]
    intro H hH
    obtain ⟨y,hy⟩ := step_total hM hw hz hzw hm hAlpha hW hb hx hi hn hmw hSucc hf hH
    exact ⟨y,hy,fun z hzv => step_unique hM hw hz hm hAlpha hf hzv hy⟩
  have hMaps : (Project.FirstOrderSemantics.reduct M).MapsSequencesInBelowInto
      (KuratowskiZF.interpretation hM) (schema.denote env) m W := by
    rw [he]
    exact fun H y _ hy => step_word hM hw hz hzw hW hi hy
  obtain ⟨H,hH,huniq⟩ := ZF.recursiveSequenceIn_existsUnique hZF
    (KuratowskiZF.interpretation hM) env schema (hw.members_areOrdinals hZF m hmw) hOperator hMaps
  rw [he] at hH huniq
  exact ⟨H,hH,fun H' hH' => huniq H' hH'⟩

def Eval (hM : FirstOrder.Theory.Models M nativeZF)
    (w D S zero mul A b W E q input y : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem input W ∧ ∃ n m f x H,
    (Project.FirstOrderSemantics.reduct M).mem n w ∧
    (Project.FirstOrderSemantics.reduct M).mem m w ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf m n ∧ MapsTo n S f ∧
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q f x ∧
    History hM w D S zero mul A b W E f x input H m ∧ PureKuratowski.PairMember M n y H

theorem eval_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hq : Raw w D S q) (hi : (Project.FirstOrderSemantics.reduct M).mem input W) :
    ∃ y, Eval hM w D S zero mul A b W E q input y := by
  obtain ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩ := hq
  obtain ⟨m,hmn,hmw⟩ := hw.1.2 n hn
  obtain ⟨H,hH,_⟩ := history_existsUnique hM hw hz hzw hm hAlpha hW hb hx hi hn hmw hmn hf
  have hMaps : MapsTo m W H := (ForcingSupportSize.native_mapsTo hM m W H).mpr hH.1.2
  obtain ⟨y,hy,_⟩ := hMaps.1.2 n hmn.predecessor_mem
  exact ⟨y,hi,n,m,f,x,H,hn,hmw,hmn,hf,hx,hq,hH,hy⟩

theorem eval_word (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y : M.Carrier .set}
    (hy : Eval hM w D S zero mul A b W E q input y) :
    (Project.FirstOrderSemantics.reduct M).mem y W := by
  obtain ⟨_,n,m,f,x,H,_,_,_,_,_,_,hH,hy⟩ := hy
  exact ((ForcingSupportSize.native_mapsTo hM m W H).mpr hH.1.2).2 n y hy

theorem eval_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y z e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hy : Eval hM w D S zero mul A b W E q input y)
    (hzv : Eval hM w D S zero mul A b W E q input z) : y = z := by
  obtain ⟨hi,n,m,f,x,H,hn,hmw,hmn,hf,hx,hq,hH,hy⟩ := hy
  obtain ⟨_,n',m',f',x',H',hn',_,hmn',hf',_,hq',hH',hzv⟩ := hzv
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  have hZF := ModelTransfer.project_models_iff.mp hM
  have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
    (native_sequence hM (hw.members_areOrdinals hZF n' hn') hf')
  subst n'
  have he := SetTheory.Structure.SuccessorOf.eq hZF.1 hmn hmn'
  subst m'
  obtain ⟨H0,_,huniq⟩ := history_existsUnique hM hw hz hzw hm hAlpha hW hb hx hi hn hmw hmn hf
  have he : H = H' := (huniq H hH).trans (huniq H' hH').symm
  subst H'
  exact ForcingConditionGraphs.function_unique
    ((ForcingSupportSize.native_mapsTo hM m W H).mpr hH.1.2).1 hy hzv

theorem eval_raw (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y : M.Carrier .set}
    (hy : Eval hM w D S zero mul A b W E q input y) : Raw w D S q := by
  obtain ⟨_,n,_,f,x,_,hn,_,_,hf,hx,hq,_,_⟩ := hy
  exact ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩


theorem eval_old_forward (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hOld : Old zero D x q) (hy : Eval hM w D S zero mul A b W E q input y) :
    OldAct w D S zero mul A x input y := by
  obtain ⟨_,n,m,f,x',H,hn,_,hmn,hf,_,hq,hH,hy⟩ := hy
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hOld.2 hq
  have hZF := ModelTransfer.project_models_iff.mp hM
  have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
    (SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)
  subst n
  obtain ⟨R,hR,hStep⟩ := hH.2 zero hmn.predecessor_mem y hy
  have hHR := hH.restriction hmn.predecessor_mem hR
  have hMaps : MapsTo zero W R := (ForcingSupportSize.native_mapsTo hM zero W R).mpr hHR.1.2
  rcases (step_at hM hw hn hMaps).mp hStep with ⟨_,ha⟩ | ⟨j,s,v,hj,_,_,_⟩
  · exact ha
  · exact (hz j hj.predecessor_mem).elim

theorem eval_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y x e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hOld : Old zero D x q) (hi : (Project.FirstOrderSemantics.reduct M).mem input W) :
    Eval hM w D S zero mul A b W E q input y ↔ OldAct w D S zero mul A x input y := by
  refine ⟨eval_old_forward hM hw hz hOld,?_⟩
  intro hy
  obtain ⟨z,hzv⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (old_raw hM hz hzw hOld) hi
  have he := oldAct_unique hM hw hz hm hAlpha.2.1 (eval_old_forward hM hw hz hOld hzv) hy
  exact he ▸ hzv

/-- Restrict the native history and use precisely the source cons append law. -/
theorem eval_cons_forward (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hCons : Cons w D S s t q) (hy : Eval hM w D S zero mul A b W E q input y) :
    ∃ v, Eval hM w D S zero mul A b W E t input v ∧ LetterAct w D S zero mul A b W E s v y := by
  obtain ⟨n,m,f,g,x,hn,hmw,hmn,hf,hg,hx,_,ht,hq,happend⟩ := hCons
  obtain ⟨hi,m',p,g',x',H,hmw',_,hpm,hg',_,hq',hH,hy⟩ := hy
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hnOrd := hw.members_areOrdinals hZF n hn
  have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF m hmw) hg)
    (native_sequence hM (hw.members_areOrdinals hZF m' hmw') hg')
  subst m'
  have hDec := cons_decomposition hM hw hn hmw hmn hf hg happend
  obtain ⟨Q,hQ,hStep⟩ := hH.2 m hpm.predecessor_mem y hy
  have hHQ := hH.restriction hpm.predecessor_mem hQ
  have hMaps : MapsTo m W Q := (ForcingSupportSize.native_mapsTo hM m W Q).mpr hHQ.1.2
  have hTail : History hM w D S zero mul A b W E f x input Q m := by
    refine ⟨hHQ.1,?_⟩
    intro k hk v hkv
    obtain ⟨R,hR,hs⟩ := hHQ.2 k hk v hkv
    have hkw := (hw.isOrdinal hZF).transitive m hmw k hk
    have hHR := hHQ.restriction hk hR
    have hMR : MapsTo k W R := (ForcingSupportSize.native_mapsTo hM k W R).mpr hHR.1.2
    refine ⟨R,hR,(step_at hM hw hkw hMR).mpr ?_⟩
    rcases (step_at hM hw hkw hMR).mp hs with hzero | ⟨j,a,z,hkj,hja,hjz,hletter⟩
    · exact Or.inl hzero
    · have hjn : (Project.FirstOrderSemantics.reduct M).mem j n := by
        rcases (hmn k).mp hk with hkn | heq
        · exact hnOrd.transitive k hkn j hkj.predecessor_mem
        · have he : k = n := (ModelTransfer.extensionality hM).eq_of_same_members k n heq
          exact he ▸ hkj.predecessor_mem
      exact Or.inr ⟨j,a,z,hkj,(hDec.prefix_restriction.2 j a).mpr ⟨hjn,hja⟩,hjz,hletter⟩
  rcases (step_at hM hw hmw hMaps).mp hStep with ⟨hempty,_⟩ | ⟨j,a,v,hmj,hja,hjv,hletter⟩
  · exact (hempty n hmn.predecessor_mem).elim
  · have he := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1 hnOrd hmn hmj
    subst j
    have he := ForcingConditionGraphs.function_unique hg.1 hja hDec.last_value
    subst a
    exact ⟨v,⟨hi,n,m,f,x,Q,hn,hmw,hmn,hf,hx,ht,hTail,hjv⟩,hletter⟩

theorem eval_cons_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E q input y s t e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hCons : Cons w D S s t q) :
    Eval hM w D S zero mul A b W E q input y ↔
      ∃ v, Eval hM w D S zero mul A b W E t input v ∧ LetterAct w D S zero mul A b W E s v y := by
  refine ⟨eval_cons_forward hM hw hCons,?_⟩
  rintro ⟨v,hv,hy⟩
  obtain ⟨z,hzv⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (cons_raw hCons).2 hv.1
  obtain ⟨v',hv',hz'⟩ := eval_cons_forward hM hw hCons hzv
  have he := eval_unique hM hw hz hzw hm hAlpha hW hb hv' hv
  subst v'
  have he := letterAct_unique hM hw hz hm hAlpha hz' hy
  exact he ▸ hzv

end PPAC.Migration.ConstructionProbeEvaluation
