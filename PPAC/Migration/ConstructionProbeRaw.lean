/- Pinned ProbeWords.Raw: actual finite words, represented by a finite internal
sequence of letters (tail-to-head) and the compulsory terminal old element.
Raw.cons uses the existing native sequence append, not an external Lean List. -/
import PPAC.Migration.ConstructionProbeLetters
import YesMetaZFC.SetTheory.Ord.FiniteSequenceParsing

namespace PPAC.Migration.ConstructionProbeRaw
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ConstructionProbeLetters (Representatives exists_representatives)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def FiniteSequence (w S f : M.Carrier .set) : Prop :=
  ∃ n, (Project.FirstOrderSemantics.reduct M).mem n w ∧ MapsTo n S f

def finiteSequence {m : Nat} (w S f : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound w.succ))
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f.succ 0 S.succ)))

theorem finiteSequence_freeClosed {m : Nat} (w S f : Fin m) : (finiteSequence w S f).FreeClosed := by
  simp -implicitDefEqProofs [finiteSequence,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem finiteSequence_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w S f : Fin m) :
    Project.Formula.satisfies env (finiteSequence w S f) ↔ FiniteSequence (env.bound w) (env.bound S) (env.bound f) := by
  simp only [finiteSequence,FiniteSequence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def Raw (w D S q : M.Carrier .set) : Prop := ∃ f x,
  FiniteSequence w S f ∧ (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q f x

def Carrier (w D S R : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q R ↔ Raw w D S q

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (D S : M.Carrier .set) : ∃ R, Carrier w D S R := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨C,hC⟩ := ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) w S
  obtain ⟨power,hPower⟩ := ZF.exists_powerSet hZF C
  let schema : Project.UnarySchema 2 := { body := finiteSequence 1 2 0, freeClosed := finiteSequence_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases w (fun _ => S), free := fun _ => w }
  obtain ⟨Q,hQ⟩ := ZF.separation_exists_d hZF schema env power
  have hQiff : ∀ f, (Project.FirstOrderSemantics.reduct M).mem f Q ↔ FiniteSequence w S f := by
    intro f
    have he : schema.denote env f ↔ FiniteSequence w S f := finiteSequence_semantics hM (env.push f) 1 2 0
    refine (hQ f).trans ⟨fun h => he.mp h.2,fun h => ?_⟩
    refine ⟨(hPower f).mpr ?_,he.mpr h⟩
    obtain ⟨n,hn,hf⟩ := h
    intro p hp
    obtain ⟨i,y,hi,hcode⟩ := hf.1.1 p hp
    exact (hC p).mpr ⟨i,(hw.isOrdinal hZF).transitive n hn i hi,y,hf.2 i y ⟨p,hcode,hp⟩,hcode⟩
  obtain ⟨R,hR⟩ := exists_representatives hM Q D
  refine ⟨R,fun q => (hR q).trans ?_⟩
  exact ⟨fun ⟨f,x,hf,hx,hcode⟩ => ⟨f,x,(hQiff f).mp hf,hx,hcode⟩,
    fun ⟨f,x,hf,hx,hcode⟩ => ⟨f,x,(hQiff f).mpr hf,hx,hcode⟩⟩

theorem native_sequence (hM : FirstOrder.Theory.Models M nativeZF) {n S f : M.Carrier .set}
    (hn : (Project.FirstOrderSemantics.reduct M).IsOrdinal n) (hf : MapsTo n S f) :
    (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength (KuratowskiZF.interpretation hM) f n := by
  have h := (ForcingSupportSize.native_mapsTo hM n S f).mp hf
  exact ⟨hn,h.1,h.2.1⟩

theorem maps_of_sequence (hM : FirstOrder.Theory.Models M nativeZF) {n S f : M.Carrier .set}
    (hf : (Project.FirstOrderSemantics.reduct M).IsSequenceOfLength (KuratowskiZF.interpretation hM) f n)
    (hrange : ∀ i y, PureKuratowski.PairMember M i y f → (Project.FirstOrderSemantics.reduct M).mem y S) :
    MapsTo n S f := by
  apply (ForcingSupportSize.native_mapsTo hM n S f).mpr
  refine ⟨hf.2.1,hf.2.2,?_⟩
  intro i hi
  obtain ⟨y,hy⟩ := (hf.2.2 i).mp hi
  exact ⟨y,hrange i y hy,hy⟩

def Old (zero D x q : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q zero x

def Cons (w D S s t q : M.Carrier .set) : Prop := ∃ n m f g x,
  (Project.FirstOrderSemantics.reduct M).mem n w ∧ (Project.FirstOrderSemantics.reduct M).mem m w ∧
  (Project.FirstOrderSemantics.reduct M).SuccessorOf m n ∧ MapsTo n S f ∧ MapsTo m S g ∧
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ (Project.FirstOrderSemantics.reduct M).mem s S ∧
  PureKuratowski.Code M t f x ∧ PureKuratowski.Code M q g x ∧
  ∀ i y, PureKuratowski.PairMember M i y g ↔ PureKuratowski.PairMember M i y f ∨ (i = n ∧ y = s)

theorem old_raw (hM : FirstOrder.Theory.Models M nativeZF) {w D S zero x q : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hOld : Old zero D x q) : Raw w D S q := by
  have hf : MapsTo zero S zero := maps_of_sequence hM (SetTheory.Structure.IsSequenceOfLength.empty
    (KuratowskiZF.interpretation hM) hz) (by intro i y h; obtain ⟨p,_,hp⟩ := h; exact (hz p hp).elim)
  exact ⟨zero,x,⟨zero,hzw,hf⟩,hOld.1,hOld.2⟩

theorem exists_old (hM : FirstOrder.Theory.Models M nativeZF) {zero D x : M.Carrier .set}
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) : ∃ q, Old zero D x q := by
  obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM zero x
  exact ⟨q,hx,hq⟩

theorem old_unique (hM : FirstOrder.Theory.Models M nativeZF) {zero D x q r : M.Carrier .set} (hq : Old zero D x q) (hr : Old zero D x r) : q = r :=
  KuratowskiZF.code_unique hM hq.2 hr.2

theorem old_injective {zero D x y q : M.Carrier .set} (hx : Old zero D x q) (hy : Old zero D y q) : x = y :=
  (PureKuratowski.code_injective hx.2 hy.2).2

theorem cons_raw {w D S s t q : M.Carrier .set} (h : Cons w D S s t q) : Raw w D S t ∧ Raw w D S q := by
  obtain ⟨n,m,f,g,x,hn,hm,_,hf,hg,hx,_,ht,hq,_⟩ := h
  exact ⟨⟨f,x,⟨n,hn,hf⟩,hx,ht⟩,⟨g,x,⟨m,hm,hg⟩,hx,hq⟩⟩

theorem exists_cons (hM : FirstOrder.Theory.Models M nativeZF) {w D S s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) (ht : Raw w D S t) : ∃ q, Cons w D S s t q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨f,x,⟨n,hn,hf⟩,hx,ht⟩ := ht
  obtain ⟨m,hmSucc,hm⟩ := hw.1.2 n hn
  obtain ⟨g,hg,hgraph⟩ := (native_sequence hM (hw.members_areOrdinals hZF n hn) hf).exists_append
    (ZF.modelsKP hZF) (KuratowskiZF.interpretation hM) (value := s) (hw.members_areOrdinals hZF m hm) hmSucc
  have hgMap := maps_of_sequence hM hg (by
    intro i y hy
    rcases (hgraph i y).mp hy with hy | ⟨_,rfl⟩
    · exact hf.2 i y hy
    · exact hs)
  obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM g x
  exact ⟨q,n,m,f,g,x,hn,hm,hmSucc,hf,hgMap,hx,hs,ht,hq,hgraph⟩

theorem cons_unique (hM : FirstOrder.Theory.Models M nativeZF) {w D S s t q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Cons w D S s t q) (hr : Cons w D S s t r) : q = r := by
  obtain ⟨n,m,f,g,x,hn,hm,hsucc,hf,hg,_,_,ht,hq,hgraph⟩ := hq
  obtain ⟨n',m',f',g',x',hn',hm',hsucc',hf',hg',_,_,ht',hr,hgraph'⟩ := hr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht'
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hnn := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
    (native_sequence hM (hw.members_areOrdinals hZF n' hn') hf')
  subst n'
  have he : g = g' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
    ((ForcingSupportSize.native_mapsTo hM m S g).mp hg).1.1
    ((ForcingSupportSize.native_mapsTo hM m' S g').mp hg').1.1
    (fun i y => (hgraph i y).trans (hgraph' i y).symm)
  subst g'
  exact KuratowskiZF.code_unique hM hq hr

theorem old_ne_cons {w D S zero x s t q : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hOld : Old zero D x q) (hCons : Cons w D S s t q) : False := by
  obtain ⟨n,m,f,g,y,_,_,_,_,_,_,_,_,hq,hgraph⟩ := hCons
  obtain ⟨rfl,_⟩ := PureKuratowski.code_injective hOld.2 hq
  obtain ⟨p,_,hp⟩ := (hgraph n s).mpr (Or.inr ⟨rfl,rfl⟩)
  exact hz p hp


/-- Native last decomposition recovers exactly the pinned Raw.cons edge law. -/
theorem decomposition_append (hM : FirstOrder.Theory.Models M nativeZF)
    {w S f n k g s : M.Carrier .set} (hf : MapsTo n S f)
    (hd : (Project.FirstOrderSemantics.reduct M).IsFiniteSequenceLastDecomposition
      (KuratowskiZF.interpretation hM) w f n k g s) :
    ∀ i y, PureKuratowski.PairMember M i y f ↔ PureKuratowski.PairMember M i y g ∨ (i = k ∧ y = s) := by
  intro i y
  constructor
  · intro hy
    rcases (hd.length_successor i).mp (ForcingConditionGraphs.function_input hf.1 hy) with hi | hi
    · exact Or.inl ((hd.prefix_restriction.2 i y).mpr ⟨hi,hy⟩)
    · have he : i = k := (ModelTransfer.extensionality hM).eq_of_same_members i k hi
      subst i
      exact Or.inr ⟨rfl,ForcingConditionGraphs.function_unique hf.1 hy hd.last_value⟩
  · rintro (hy | ⟨rfl,rfl⟩)
    · exact ((hd.prefix_restriction.2 i y).mp hy).2
    · exact hd.last_value

/-- Every internal Raw value has precisely the source old/cons cases. -/
theorem cases_raw (hM : FirstOrder.Theory.Models M nativeZF) {w D S zero q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hq : Raw w D S q) : (∃ x, Old zero D x q) ∨ ∃ s t, Cons w D S s t q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨f,x,⟨n,hn,hf⟩,hx,hcode⟩ := hq
  have hseq := native_sequence hM (hw.members_areOrdinals hZF n hn) hf
  rcases SetTheory.Structure.IsFiniteSequenceLastDecomposition.empty_or_decomposition_exists_unique
      hZF (KuratowskiZF.interpretation hM) hw ⟨hn,hseq⟩ with hempty | ⟨k,g,s,hd,_⟩
  · have he : f = zero := SetTheory.Structure.IsFiniteSequenceOfLength.empty_sequence_unique
      hZF.1 ⟨hn,hseq⟩ ⟨hzw,SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz⟩ hempty hz
    subst f
    exact Or.inl ⟨x,hx,hcode⟩
  · have hg : MapsTo k S g := maps_of_sequence hM hd.prefix_sequence.2
      (fun i y hy => hf.2 i y ((hd.prefix_restriction.2 i y).mp hy).2)
    obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM g x
    exact Or.inr ⟨s,t,k,n,g,f,x,hd.predecessor_mem_omega,hn,hd.length_successor,hg,hf,
      hx,hf.2 k s hd.last_value,ht,hcode,decomposition_append hM hf hd⟩

/-- The append used by Raw.cons is the existing native last decomposition. -/
theorem cons_decomposition (hM : FirstOrder.Theory.Models M nativeZF)
    {w S n m f g s : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n)
    (hf : MapsTo n S f) (hg : MapsTo m S g)
    (he : ∀ i y, PureKuratowski.PairMember M i y g ↔ PureKuratowski.PairMember M i y f ∨ (i = n ∧ y = s)) :
    (Project.FirstOrderSemantics.reduct M).IsFiniteSequenceLastDecomposition
      (KuratowskiZF.interpretation hM) w g m n f s := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hnOrd := hw.members_areOrdinals hZF n hn
  refine ⟨⟨hm,native_sequence hM (hw.members_areOrdinals hZF m hm) hg⟩,hn,hSucc,
    ⟨hn,native_sequence hM hnOrd hf⟩,⟨((ForcingSupportSize.native_mapsTo hM n S f).mp hf).1.1,?_⟩,
    (he n s).mpr (Or.inr ⟨rfl,rfl⟩)⟩
  intro i y
  constructor
  · intro hy
    exact ⟨ForcingConditionGraphs.function_input hf.1 hy,(he i y).mpr (Or.inl hy)⟩
  · rintro ⟨hi,hy⟩
    rcases (he i y).mp hy with hy | ⟨rfl,_⟩
    · exact hy
    · exact (hnOrd.wellOrder.linear.irrefl i hi hi).elim

theorem cons_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S s t s' t' q : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Cons w D S s t q) (hr : Cons w D S s' t' q) : s = s' ∧ t = t' := by
  obtain ⟨n,m,f,g,x,hn,hm,hsucc,hf,hg,_,_,ht,hq,he⟩ := hq
  obtain ⟨n',m',f',g',x',hn',hm',hsucc',hf',hg',_,_,ht',hr,he'⟩ := hr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hr
  have hd := cons_decomposition hM hw hn hm hsucc hf hg he
  have hd' := cons_decomposition hM hw hn' hm' hsucc' hf' hg' he'
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hmEq := SetTheory.Structure.IsFiniteSequenceOfLength.length_unique hZF.1 hd.source hd'.source
  subst m'
  obtain ⟨_,hfEq,hsEq⟩ := SetTheory.Structure.IsFiniteSequenceLastDecomposition.components_unique hZF.1 hd hd'
  subst f'
  exact ⟨hsEq,KuratowskiZF.code_unique hM ht ht'⟩


def raw {m : Nat} (w D S q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (finiteSequence w.succ.succ S.succ.succ 1) (.conj (.mem (.bound 0) (.bound
    D.succ.succ)) (ProjectSyntax.encode id (PairSyntax.ordered q.succ.succ 1 0))))))

theorem raw_freeClosed {m : Nat} (w D S q : Fin m) : (raw w D S q).FreeClosed := by
  simp -implicitDefEqProofs [raw,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    finiteSequence_freeClosed]

theorem raw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S q : Fin m) :
    Project.Formula.satisfies env (raw w D S q) ↔ Raw (env.bound w) (env.bound D) (env.bound S) (env.bound q) := by
  simp only [raw,Raw,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    finiteSequence_semantics hM]
  rfl

def carrier {m : Nat} (w D S R : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound R.succ)) (raw w.succ D.succ S.succ 0)))

theorem carrier_freeClosed {m : Nat} (w D S R : Fin m) : (carrier w D S R).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,
    raw_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S R : Fin m) :
    Project.Formula.satisfies env (carrier w D S R) ↔ Carrier (env.bound w) (env.bound D) (env.bound S) (env.bound R) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,raw_semantics hM]
  rfl

def old {m : Nat} (zero D x q : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound x) (.bound D)) (ProjectSyntax.encode id (PairSyntax.ordered q zero x)))

theorem old_freeClosed {m : Nat} (zero D x q : Fin m) : (old zero D x q).FreeClosed := by
  simp -implicitDefEqProofs [old,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem old_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D x q : Fin m) :
    Project.Formula.satisfies env (old zero D x q) ↔ Old (env.bound zero) (env.bound D) (env.bound x) (env.bound q) := by
  simp only [old,Old,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_code]
  rfl

def cons {m : Nat} (w D S a t q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4) (.bound
    w.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 3) (.bound w.succ.succ.succ.succ.succ)) (.conj
    (Project.Formula.isSuccessor (.bound 3) (.bound 4)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 2 4 S.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 1 3 S.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 0) (.bound
    D.succ.succ.succ.succ.succ)) (.conj (.mem (.bound a.succ.succ.succ.succ.succ) (.bound
    S.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (PairSyntax.ordered
    t.succ.succ.succ.succ.succ 2 0)) (.conj (ProjectSyntax.encode id (PairSyntax.ordered
    q.succ.succ.succ.succ.succ 1 0)) (.forallE (.forallE (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge 3 1 0)) (.disj (ProjectSyntax.encode id (Source.SetLanguage.edge 4 1 0)) (.conj
    (Project.Formula.extensionalEq (.bound 1) (.bound 6)) (Project.Formula.extensionalEq (.bound 0) (.bound
    a.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))

theorem cons_freeClosed {m : Nat} (w D S a t q : Fin m) : (cons w D S a t q).FreeClosed := by
  simp -implicitDefEqProofs [cons,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isSuccessor,Project.Formula.extensionalEq_freeClosed_iff]

theorem cons_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S a t q : Fin m) :
    Project.Formula.satisfies env (cons w D S a t q) ↔ Cons (env.bound w) (env.bound D) (env.bound S) (env.bound a) (env.bound t) (env.bound q) := by
  simp only [cons,Cons,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def ConstructorLaws (w D S zero : M.Carrier .set) : Prop :=
  (∀ x, (Project.FirstOrderSemantics.reduct M).mem x D → ∃ q, Old zero D x q) ∧
  (∀ x q r, Old zero D x q → Old zero D x r → q = r) ∧
  (∀ x y q, Old zero D x q → Old zero D y q → x = y) ∧
  (∀ x q, Old zero D x q → Raw w D S q) ∧
  (∀ a t, (Project.FirstOrderSemantics.reduct M).mem a S → Raw w D S t → ∃ q, Cons w D S a t q) ∧
  (∀ a t q r, Cons w D S a t q → Cons w D S a t r → q = r) ∧
  (∀ a t b v q, Cons w D S a t q → Cons w D S b v q → a = b ∧ t = v) ∧
  (∀ a t q, Cons w D S a t q → Raw w D S t ∧ Raw w D S q) ∧
  (∀ x a t q, Old zero D x q → ¬ Cons w D S a t q) ∧
  (∀ q, Raw w D S q → (∃ x, Old zero D x q) ∨ ∃ a t, Cons w D S a t q)

theorem constructor_laws (hM : FirstOrder.Theory.Models M nativeZF) {w D S zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) : ConstructorLaws w D S zero := by
  exact ⟨fun _ hx => exists_old hM hx,fun _ _ _ => old_unique hM,fun _ _ _ => old_injective,
    fun _ _ => old_raw hM hz hzw,fun _ _ hs ht => exists_cons hM hw hs ht,
    fun _ _ _ _ => cons_unique hM hw,fun _ _ _ _ _ => cons_injective hM hw,
    fun _ _ _ => cons_raw,fun _ _ _ _ ho hc => old_ne_cons hz ho hc,fun _ => cases_raw hM hw hz hzw⟩

def constructorLaws {m : Nat} (w D S zero : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (.mem (.bound 0) (.bound D.succ)) (.existsE (old zero.succ.succ D.succ.succ 1 0))))
    (.conj (.forallE (.forallE (.forallE (.imp (old zero.succ.succ.succ D.succ.succ.succ 2 1) (.imp (old
    zero.succ.succ.succ D.succ.succ.succ 2 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))
    (.conj (.forallE (.forallE (.forallE (.imp (old zero.succ.succ.succ D.succ.succ.succ 2 0) (.imp (old
    zero.succ.succ.succ D.succ.succ.succ 1 0) (Project.Formula.extensionalEq (.bound 2) (.bound 1)))))))
    (.conj (.forallE (.forallE (.imp (old zero.succ.succ D.succ.succ 1 0) (raw w.succ.succ D.succ.succ
    S.succ.succ 0)))) (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound S.succ.succ)) (.imp (raw
    w.succ.succ D.succ.succ S.succ.succ 0) (.existsE (cons w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ
    2 1 0)))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (cons w.succ.succ.succ.succ
    D.succ.succ.succ.succ S.succ.succ.succ.succ 3 2 1) (.imp (cons w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ 3 2 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))) (.conj (.forallE
    (.forallE (.forallE (.forallE (.forallE (.imp (cons w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ 4 3 0) (.imp (cons w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ 2 1 0) (.conj (Project.Formula.extensionalEq (.bound 4) (.bound 2))
    (Project.Formula.extensionalEq (.bound 3) (.bound 1)))))))))) (.conj (.forallE (.forallE (.forallE (.imp
    (cons w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 2 1 0) (.conj (raw w.succ.succ.succ
    D.succ.succ.succ S.succ.succ.succ 1) (raw w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 0))))))
    (.conj (.forallE (.forallE (.forallE (.forallE (.imp (old zero.succ.succ.succ.succ D.succ.succ.succ.succ 3
    0) (.neg (cons w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ 2 1 0))))))) (.forallE
    (.imp (raw w.succ D.succ S.succ 0) (.disj (.existsE (old zero.succ.succ D.succ.succ 0 1)) (.existsE
    (.existsE (cons w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 1 0 2)))))))))))))))

theorem constructorLaws_freeClosed {m : Nat} (w D S zero : Fin m) :
    (constructorLaws w D S zero).FreeClosed := by
  simp -implicitDefEqProofs [constructorLaws,Definitional.Formula.FreeClosed,
    Project.Formula.extensionalEq_freeClosed_iff,old_freeClosed,cons_freeClosed,raw_freeClosed]

theorem constructorLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero : Fin m) :
    Project.Formula.satisfies env (constructorLaws w D S zero) ↔
      ConstructorLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) := by
  simp only [constructorLaws,ConstructorLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    old_semantics hM,cons_semantics hM,raw_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isEmpty (.bound 3))
        (.imp (.mem (.bound 3) (.bound 0))
          (.existsE (.conj (carrier (1 : Fin 5) 2 3 0) (constructorLaws (1 : Fin 5) 2 3 4))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    Project.Formula.isEmpty,carrier_freeClosed,constructorLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,carrier_semantics hM,
    constructorLaws_semantics hM]
  intro hw hz hzw
  obtain ⟨R,hR⟩ := exists_carrier hM hw (bound 1) (bound 2)
  exact ⟨R,hR,constructor_laws hM hw hz hzw⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeRaw
