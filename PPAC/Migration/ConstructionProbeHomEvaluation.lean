/- Pinned ProbeWords.Word.evalHom: interpret a Raw word in an arbitrary
internal binary algebra. Native bounded recursion supplies the exact old/cons
fold; no cancellation, external standard length or new recursion backend. -/
import PPAC.Migration.ConstructionProbeRaw
import PPAC.Migration.ConstructionProbeAction

namespace PPAC.Migration.ConstructionProbeHomEvaluation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range)
open ForcingDiagramOrder (Product)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem product_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J N mulN x y z z' : M.Carrier .set} (hMul : MapsTo J N mulN)
    (hz : Product mulN x y z) (hz' : Product mulN x y z') : z = z' := by
  obtain ⟨p,hp,hz⟩ := hz
  obtain ⟨p',hp',hz'⟩ := hz'
  have he := KuratowskiZF.code_unique hM hp hp'
  subst p'
  exact ForcingConditionGraphs.function_unique hMul.1 hz hz'

def Prepend (Q mulN s v y : M.Carrier .set) : Prop :=
  ∃ a, PureKuratowski.PairMember M s a Q ∧ Product mulN a v y

theorem prepend_total (hM : FirstOrder.Theory.Models M nativeZF)
    {S N J mulN Q s v : M.Carrier .set}
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hQ : MapsTo S N Q)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hv : (Project.FirstOrderSemantics.reduct M).mem v N) : ∃ y, Prepend Q mulN s v y := by
  obtain ⟨a,ha,_⟩ := hQ.1.2 s hs
  obtain ⟨y,_,hy⟩ := projected hM hJ hMul (hQ.2 s a ha) hv
  exact ⟨y,a,ha,hy⟩

theorem prepend_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {S N J mulN Q s v y z : M.Carrier .set} (hMul : MapsTo J N mulN) (hQ : MapsTo S N Q)
    (hy : Prepend Q mulN s v y) (hz : Prepend Q mulN s v z) : y = z := by
  obtain ⟨a,ha,hy⟩ := hy
  obtain ⟨a',ha',hz⟩ := hz
  have he := ForcingConditionGraphs.function_unique hQ.1 ha ha'
  subst a'
  exact product_unique hM hMul hy hz

theorem prepend_range {N J mulN Q s v y : M.Carrier .set}
    (hMul : MapsTo J N mulN) (hy : Prepend Q mulN s v y) :
    (Project.FirstOrderSemantics.reduct M).mem y N := by
  obtain ⟨a,_,hy⟩ := hy
  exact projected_range hMul hy

def Step (w N mulN F Q f x H y : M.Carrier .set) : Prop := ∃ k,
  (Project.FirstOrderSemantics.reduct M).mem k w ∧ MapsTo k N H ∧
  (((∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i k) ∧ PureKuratowski.PairMember M x y F) ∨
    ∃ j s v, (Project.FirstOrderSemantics.reduct M).SuccessorOf k j ∧
      PureKuratowski.PairMember M j s f ∧ PureKuratowski.PairMember M j v H ∧ Prepend Q mulN s v y)

theorem step_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w N mulN F Q f x H y k : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k w) (hH : MapsTo k N H) :
    Step w N mulN F Q f x H y ↔
      (((∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i k) ∧ PureKuratowski.PairMember M x y F) ∨
        ∃ j s v, (Project.FirstOrderSemantics.reduct M).SuccessorOf k j ∧
          PureKuratowski.PairMember M j s f ∧ PureKuratowski.PairMember M j v H ∧
            Prepend Q mulN s v y) := by
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
    {w D S N J mulN F Q f x H y z n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q) (hf : MapsTo n S f)
    (hy : Step w N mulN F Q f x H y) (hz : Step w N mulN F Q f x H z) : y = z := by
  obtain ⟨k,hk,hH,hy⟩ := hy
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hkOrd := hw.members_areOrdinals hZF k hk
  have hz := (step_at hM hw hk hH).mp hz
  rcases hy with ⟨hempty,hy⟩ | ⟨j,s,v,hkj,hjs,hjv,hy⟩
  · rcases hz with ⟨_,hz⟩ | ⟨j,s,v,hkj,_,_,_⟩
    · exact ForcingConditionGraphs.function_unique hF.1 hy hz
    · exact (hempty j hkj.predecessor_mem).elim
  · rcases hz with ⟨hempty,_⟩ | ⟨j',s',v',hkj',hjs',hjv',hz⟩
    · exact (hempty j hkj.predecessor_mem).elim
    · have he := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1
        (hkOrd.mem hkj.predecessor_mem) hkj hkj'
      subst j'
      have he := ForcingConditionGraphs.function_unique hf.1 hjs hjs'
      subst s'
      have he := ForcingConditionGraphs.function_unique hH.1 hjv hjv'
      subst v'
      exact prepend_unique hM hMul hQ hy hz

theorem step_range {w D N J mulN F Q f x H y : M.Carrier .set}
    (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hy : Step w N mulN F Q f x H y) :
    (Project.FirstOrderSemantics.reduct M).mem y N := by
  obtain ⟨_,_,_,hy⟩ := hy
  rcases hy with ⟨_,hy⟩ | ⟨j,s,v,_,_,_,hy⟩
  · exact hF.2 x y hy
  · exact prepend_range hMul hy

theorem step_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J mulN F Q f x H n m : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hmw : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n) (hf : MapsTo n S f)
    (hH : (Project.FirstOrderSemantics.reduct M).IsSequenceInBelow (KuratowskiZF.interpretation hM) H m N) :
    ∃ y, Step w N mulN F Q f x H y := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨_,k,hkm,hH⟩ := hH
  have hk : (Project.FirstOrderSemantics.reduct M).mem k w := (hw.isOrdinal hZF).transitive m hmw k hkm
  have hMaps : MapsTo k N H := (ForcingSupportSize.native_mapsTo hM k N H).mpr hH.2
  by_cases hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i k
  · obtain ⟨j,hjw,hkj⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hk hne
    have hjn : (Project.FirstOrderSemantics.reduct M).mem j n := by
      rcases (hSucc k).mp hkm with hkn | heq
      · exact (hw.members_areOrdinals hZF n hn).transitive k hkn j hkj.predecessor_mem
      · have he : k = n := (ModelTransfer.extensionality hM).eq_of_same_members k n heq
        exact he ▸ hkj.predecessor_mem
    obtain ⟨s,hjs,_⟩ := hf.1.2 j hjn
    obtain ⟨v,hjv,_⟩ := hMaps.1.2 j hkj.predecessor_mem
    obtain ⟨y,hy⟩ := prepend_total hM hJ hMul hQ (hf.2 j s hjs) (hMaps.2 j v hjv)
    exact ⟨y,k,hk,hMaps,Or.inr ⟨j,s,v,hkj,hjs,hjv,hy⟩⟩
  · obtain ⟨y,hy,_⟩ := hF.1.2 x hx
    exact ⟨y,k,hk,hMaps,Or.inl ⟨fun i hi => hne ⟨i,hi⟩,hy⟩⟩

def prepend {m : Nat} (Q mulN s v y : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Q.succ s.succ 0)) (ProjectSyntax.encode
    id (ForcingDiagramOrder.product mulN.succ 0 v.succ y.succ))))

theorem prepend_freeClosed {m : Nat} (Q mulN s v y : Fin m) : (prepend Q mulN s v y).FreeClosed := by
  simp -implicitDefEqProofs [prepend,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem prepend_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Q mulN s v y : Fin m) :
    Project.Formula.satisfies env (prepend Q mulN s v y) ↔
      Prepend (env.bound Q) (env.bound mulN) (env.bound s) (env.bound v) (env.bound y) := by
  simp only [prepend,Prepend,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def step {m : Nat} (w N mulN F Q f x H y : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (.mem (.bound 0) (.bound w.succ)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo H.succ 0 N.succ)) (.disj (.conj (Project.Formula.isEmpty (.bound 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ x.succ y.succ))) (.existsE (.existsE (.existsE
    (.conj (Project.Formula.isSuccessor (.bound 3) (.bound 2)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ.succ.succ 2 1)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge H.succ.succ.succ.succ 2 0)) (prepend Q.succ.succ.succ.succ
    mulN.succ.succ.succ.succ 1 0 y.succ.succ.succ.succ)))))))))))

theorem step_freeClosed {m : Nat} (w N mulN F Q f x H y : Fin m) :
    (step w N mulN F Q f x H y).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,prepend_freeClosed,
    Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.extensionalEq_freeClosed_iff]

theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N mulN F Q f x H y : Fin m) :
    Project.Formula.satisfies env (step w N mulN F Q f x H y) ↔
      Step (env.bound w) (env.bound N) (env.bound mulN) (env.bound F) (env.bound Q) (env.bound f)
        (env.bound x) (env.bound H) (env.bound y) := by
  simp only [step,Step,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    KuratowskiZF.source_edge,prepend_semantics hM]
  rfl

def stepSchema {m : Nat} (w N mulN F Q f x : Fin m) : Project.BinarySchema m where
  body := step w.succ.succ N.succ.succ mulN.succ.succ F.succ.succ Q.succ.succ f.succ.succ x.succ.succ 1 0
  freeClosed := step_freeClosed _ _ _ _ _ _ _ _ _

theorem stepSchema_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N mulN F Q f x : Fin m) (H y : M.Carrier .set) :
    (stepSchema w N mulN F Q f x).denote env H y ↔
      Step (env.bound w) (env.bound N) (env.bound mulN) (env.bound F) (env.bound Q) (env.bound f) (env.bound x) H y :=
  step_semantics hM ((env.push H).push y) w.succ.succ N.succ.succ mulN.succ.succ F.succ.succ Q.succ.succ f.succ.succ x.succ.succ 1 0

def History (hM : FirstOrder.Theory.Models M nativeZF) (w N mulN F Q f x H m : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsRecursiveSequenceIn (KuratowskiZF.interpretation hM)
    (Step w N mulN F Q f x) H m N

theorem history_existsUnique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J mulN F Q f x n m : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hmw : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n) (hf : MapsTo n S f) :
    ∃ H, History hM w N mulN F Q f x H m ∧
      ∀ H', History hM w N mulN F Q f x H' m → H' = H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases w (Fin.cases N (Fin.cases mulN (Fin.cases F (Fin.cases Q (Fin.cases f (fun _ => x)))))),
    free := fun _ => w }
  let schema := stepSchema (0 : Fin 7) 1 2 3 4 5 6
  have he : schema.denote env = Step w N mulN F Q f x := by
    funext H y
    exact propext (stepSchema_semantics hM env 0 1 2 3 4 5 6 H y)
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hOperator : (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnSequencesInBelow
      (KuratowskiZF.interpretation hM) (schema.denote env) m N := by
    rw [he]
    intro H hH
    obtain ⟨y,hy⟩ := step_total hM hw hJ hMul hF hQ hx hn hmw hSucc hf hH
    exact ⟨y,hy,fun z hz => step_unique hM hw hMul hF hQ hf hz hy⟩
  have hMaps : (Project.FirstOrderSemantics.reduct M).MapsSequencesInBelowInto
      (KuratowskiZF.interpretation hM) (schema.denote env) m N := by
    rw [he]
    exact fun H y _ hy => step_range hMul hF hy
  obtain ⟨H,hH,huniq⟩ := ZF.recursiveSequenceIn_existsUnique hZF
    (KuratowskiZF.interpretation hM) env schema (hw.members_areOrdinals hZF m hmw) hOperator hMaps
  rw [he] at hH huniq
  exact ⟨H,hH,fun H' hH' => huniq H' hH'⟩

def Eval (hM : FirstOrder.Theory.Models M nativeZF) (w D S N mulN F Q q y : M.Carrier .set) : Prop :=
  ∃ n m f x H, (Project.FirstOrderSemantics.reduct M).mem n w ∧
    (Project.FirstOrderSemantics.reduct M).mem m w ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf m n ∧ MapsTo n S f ∧
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q f x ∧
    History hM w N mulN F Q f x H m ∧ PureKuratowski.PairMember M n y H

theorem eval_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J mulN F Q q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hq : Raw w D S q) : ∃ y, Eval hM w D S N mulN F Q q y := by
  obtain ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩ := hq
  obtain ⟨m,hmn,hmw⟩ := hw.1.2 n hn
  obtain ⟨H,hH,_⟩ := history_existsUnique hM hw hJ hMul hF hQ hx hn hmw hmn hf
  have hMaps : MapsTo m N H := (ForcingSupportSize.native_mapsTo hM m N H).mpr hH.1.2
  obtain ⟨y,hy,_⟩ := hMaps.1.2 n hmn.predecessor_mem
  exact ⟨y,n,m,f,x,H,hn,hmw,hmn,hf,hx,hq,hH,hy⟩

theorem eval_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N mulN F Q q y : M.Carrier .set} (hy : Eval hM w D S N mulN F Q q y) :
    (Project.FirstOrderSemantics.reduct M).mem y N := by
  obtain ⟨n,m,f,x,H,_,_,_,_,_,_,hH,hy⟩ := hy
  exact ((ForcingSupportSize.native_mapsTo hM m N H).mpr hH.1.2).2 n y hy

theorem eval_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J mulN F Q q y z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hy : Eval hM w D S N mulN F Q q y) (hz : Eval hM w D S N mulN F Q q z) : y = z := by
  obtain ⟨n,m,f,x,H,hn,hmw,hmn,hf,hx,hq,hH,hy⟩ := hy
  obtain ⟨n',m',f',x',H',hn',_,hmn',hf',_,hq',hH',hz⟩ := hz
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  have hZF := ModelTransfer.project_models_iff.mp hM
  have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
    (native_sequence hM (hw.members_areOrdinals hZF n' hn') hf')
  subst n'
  have he := SetTheory.Structure.SuccessorOf.eq hZF.1 hmn hmn'
  subst m'
  obtain ⟨H0,_,huniq⟩ := history_existsUnique hM hw hJ hMul hF hQ hx hn hmw hmn hf
  have he : H = H' := (huniq H hH).trans (huniq H' hH').symm
  subst H'
  exact ForcingConditionGraphs.function_unique ((ForcingSupportSize.native_mapsTo hM m N H).mpr hH.1.2).1 hy hz

theorem eval_raw (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N mulN F Q q y : M.Carrier .set} (hy : Eval hM w D S N mulN F Q q y) : Raw w D S q := by
  obtain ⟨n,_,f,x,_,hn,_,_,hf,hx,hq,_,_⟩ := hy
  exact ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩

theorem eval_old_forward (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero N mulN F Q q y x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hOld : Old zero D x q) (hy : Eval hM w D S N mulN F Q q y) :
    PureKuratowski.PairMember M x y F := by
  obtain ⟨n,m,f,x',H,hn,_,hmn,hf,_,hq,hH,hy⟩ := hy
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hOld.2 hq
  have hZF := ModelTransfer.project_models_iff.mp hM
  have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
    (SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)
  subst n
  obtain ⟨R,hR,hStep⟩ := hH.2 zero hmn.predecessor_mem y hy
  have hHR := hH.restriction hmn.predecessor_mem hR
  have hMaps : MapsTo zero N R := (ForcingSupportSize.native_mapsTo hM zero N R).mpr hHR.1.2
  rcases (step_at hM hw hn hMaps).mp hStep with ⟨_,ha⟩ | ⟨j,s,v,hj,_,_,_⟩
  · exact ha
  · exact (hz j hj.predecessor_mem).elim

theorem eval_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero N J mulN F Q q y x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hOld : Old zero D x q) : Eval hM w D S N mulN F Q q y ↔ PureKuratowski.PairMember M x y F := by
  refine ⟨eval_old_forward hM hw hz hOld,?_⟩
  intro hy
  obtain ⟨z,hzv⟩ := eval_total hM hw hJ hMul hF hQ (old_raw hM hz hzw hOld)
  have he := ForcingConditionGraphs.function_unique hF.1 (eval_old_forward hM hw hz hOld hzv) hy
  exact he ▸ hzv

/-- Restrict the native history and use precisely the source cons append law. -/
theorem eval_cons_forward (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N mulN F Q q y s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hCons : Cons w D S s t q) (hy : Eval hM w D S N mulN F Q q y) :
    ∃ v, Eval hM w D S N mulN F Q t v ∧ Prepend Q mulN s v y := by
  obtain ⟨n,m,f,g,x,hn,hmw,hmn,hf,hg,hx,_,ht,hq,happend⟩ := hCons
  obtain ⟨m',p,g',x',H,hmw',_,hpm,hg',_,hq',hH,hy⟩ := hy
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hnOrd := hw.members_areOrdinals hZF n hn
  have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF m hmw) hg)
    (native_sequence hM (hw.members_areOrdinals hZF m' hmw') hg')
  subst m'
  have hDec := cons_decomposition hM hw hn hmw hmn hf hg happend
  obtain ⟨H0,hQ,hStep⟩ := hH.2 m hpm.predecessor_mem y hy
  have hHQ := hH.restriction hpm.predecessor_mem hQ
  have hMaps : MapsTo m N H0 := (ForcingSupportSize.native_mapsTo hM m N H0).mpr hHQ.1.2
  have hTail : History hM w N mulN F Q f x H0 m := by
    refine ⟨hHQ.1,?_⟩
    intro k hk v hkv
    obtain ⟨R,hR,hs⟩ := hHQ.2 k hk v hkv
    have hkw := (hw.isOrdinal hZF).transitive m hmw k hk
    have hHR := hHQ.restriction hk hR
    have hMR : MapsTo k N R := (ForcingSupportSize.native_mapsTo hM k N R).mpr hHR.1.2
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
    exact ⟨v,⟨n,m,f,x,H0,hn,hmw,hmn,hf,hx,ht,hTail,hjv⟩,hletter⟩

theorem eval_cons_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J mulN F Q q y s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hCons : Cons w D S s t q) : Eval hM w D S N mulN F Q q y ↔
      ∃ v, Eval hM w D S N mulN F Q t v ∧ Prepend Q mulN s v y := by
  refine ⟨eval_cons_forward hM hw hCons,?_⟩
  rintro ⟨v,hv,hy⟩
  obtain ⟨z,hz⟩ := eval_total hM hw hJ hMul hF hQ (cons_raw hCons).2
  obtain ⟨v',hv',hz'⟩ := eval_cons_forward hM hw hCons hz
  have he := eval_unique hM hw hJ hMul hF hQ hv' hv
  subst v'
  have he := prepend_unique hM hMul hQ hz' hy
  exact he ▸ hz

end PPAC.Migration.ConstructionProbeHomEvaluation
