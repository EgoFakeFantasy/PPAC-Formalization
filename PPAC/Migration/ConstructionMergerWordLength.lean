/- Pinned MergerWords.Word.length_old/snoc/act/mul:160-170.
Use the EXISTING internal finite sequence length and native ordinal addition;
no external Nat recursion, parser, packet encoding or new arithmetic backend.
Consumer: source product_left_cancel's old/snoc length contradiction. -/
import PPAC.Migration.ConstructionMergerWordMonoid

namespace PPAC.Migration.ConstructionMergerWordLength
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionMergerWordAction (Act ActionTable)
open ConstructionMergerWordProduct (Laws)
open ConstructionBaseMonoid (AdditionGraph)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Length (w D L q n : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem n w ∧ ∃ f x, MapsTo n L f ∧
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q f x

theorem length_raw {w D L q n : M.Carrier .set} (h : Length w D L q n) : Raw w D L q := by
  obtain ⟨hn,f,x,hf,hx,hq⟩ := h
  exact ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩

theorem exists_length {w D L q : M.Carrier .set} (h : Raw w D L q) : ∃ n, Length w D L q n := by
  obtain ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩ := h
  exact ⟨n,hn,f,x,hf,hx,hq⟩

theorem length_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L q n m : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : Length w D L q n) (hm : Length w D L q m) : n = m := by
  obtain ⟨hnw,f,x,hf,_,hq⟩ := hn
  obtain ⟨hmw,f',x',hf',_,hq'⟩ := hm
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  have hZF := ModelTransfer.project_models_iff.mp hM
  exact SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hnw) hf)
    (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF m hmw) hf')

theorem old_length (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero x q n : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hOld : Old zero D x q) (hn : Length w D L q n) : n = zero := by
  obtain ⟨hnw,f,x',hf,_,hq⟩ := hn
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hOld.2 hq
  have hZF := ModelTransfer.project_models_iff.mp hM
  exact SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
    (ConstructionProbeRaw.native_sequence hM (hw.members_areOrdinals hZF n hnw) hf)
    (SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)

theorem cons_lengths {w D L s t q : M.Carrier .set} (hc : Cons w D L s t q) :
    ∃ n m, Length w D L t n ∧ Length w D L q m ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf m n := by
  obtain ⟨n,m,f,g,x,hn,hm,hsucc,hf,hg,hx,_,ht,hq,_⟩ := hc
  exact ⟨n,m,⟨hn,f,x,hf,hx,ht⟩,⟨hm,g,x,hg,hx,hq⟩,hsucc⟩

theorem cons_length (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L s t q n m : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hc : Cons w D L s t q) (hn : Length w D L t n) (hm : Length w D L q m) :
    (Project.FirstOrderSemantics.reduct M).SuccessorOf m n := by
  obtain ⟨n',m',hn',hm',hsucc⟩ := cons_lengths hc
  have heN := length_unique hM hw hn' hn
  have heM := length_unique hM hw hm' hm
  exact heM ▸ heN ▸ hsucc

theorem act_length (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A q x out n m : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (ha : Act w D L zero mul A q x out) (hn : Length w D L q n) (hm : Length w D L out m) : n = m := by
  rcases ha.2 with ⟨a,ax,hOld,_,hOut⟩ | ⟨s,t,sx,hCons,_,hOut⟩
  · exact (old_length hM hw hz hOld hn).trans (old_length hM hw hz hOut hm).symm
  · obtain ⟨k,hk⟩ := exists_length (ConstructionProbeRaw.cons_raw hCons).1
    exact SetTheory.Structure.SuccessorOf.eq (ModelTransfer.extensionality hM)
      (cons_length hM hw hCons hk hn) (cons_length hM hw hOut hk hm)

def length {m0 : Nat} (w D L q n : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.mem (.bound n) (.bound w)) (.existsE (.existsE (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo 1 n.succ.succ L.succ.succ)) (.conj (.mem (.bound 0) (.bound D.succ.succ))
  (PureKuratowskiProject.code (.bound q.succ.succ) (.bound 1) (.bound 0)))))))

theorem length_freeClosed {m0 : Nat} (w D L q n : Fin m0) : (length w D L q n).FreeClosed := by
  simp -implicitDefEqProofs [length,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem length_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L q n : Fin m0) :
    Project.Formula.satisfies env (length w D L q n) ↔ Length (env.bound w) (env.bound D) (env.bound L) (env.bound q) (env.bound n) := by
  simp only [length,Length,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def lengthProductAt {m0 : Nat} (w D L W plus H q : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 4) (.bound
  W.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  H.succ.succ.succ.succ.succ 4 q.succ.succ.succ.succ.succ 3)) (.imp (length w.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ 4 2) (.imp (length w.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 1) (.imp (length
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ 3 0)
  (ProjectSyntax.encode id (ForcingDiagramOrder.product plus.succ.succ.succ.succ.succ 2 1 0))))))))))))

theorem lengthProductAt_freeClosed {m0 : Nat} (w D L W plus H q : Fin m0) : (lengthProductAt w D L W plus H q).FreeClosed := by
  simp -implicitDefEqProofs [lengthProductAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,length_freeClosed]

theorem lengthProductAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L W plus H q : Fin m0) :
    Project.Formula.satisfies env (lengthProductAt w D L W plus H q) ↔
      ∀ left out a b c, (Project.FirstOrderSemantics.reduct M).mem left (env.bound W) →
        Product (env.bound H) left (env.bound q) out → Length (env.bound w) (env.bound D) (env.bound L) left a →
        Length (env.bound w) (env.bound D) (env.bound L) (env.bound q) b →
        Length (env.bound w) (env.bound D) (env.bound L) out c → Product (env.bound plus) a b c := by
  simp only [lengthProductAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,length_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

theorem product_length (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W plus H T left right out a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hAdd : AdditionGraph hM w plus)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hl : (Project.FirstOrderSemantics.reduct M).mem left W) (hp : Product H left right out)
    (ha : Length w D L left a) (hb : Length w D L right b) (hc : Length w D L out c) : Product plus a b c := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hPlusMono := ConstructionBaseMonoid.leftCancelMonoid hM hw hAdd hz hzw
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases L (Fin.cases W (Fin.cases plus (fun _ => H))))),free := fun _ => w }
  let p : Project.UnarySchema 6 := { body := lengthProductAt 1 2 3 4 5 6 0,freeClosed := lengthProductAt_freeClosed _ _ _ _ _ _ _ }
  have he (q) : p.denote env q ↔ ∀ left out a b c,
      (Project.FirstOrderSemantics.reduct M).mem left W → Product H left q out →
      Length w D L left a → Length w D L q b → Length w D L out c → Product plus a b c :=
    lengthProductAt_semantics hM (env.push q) 1 2 3 4 5 6 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro left out a b c _ hProd ha hb hc
    have heB := old_length hM hw hz hOld hb
    subst b
    have hAct := (hTable left x out).mp ((hLaws.1 x left q out hOld).mp hProd)
    have heC := act_length hM hw hz hAct ha hc
    subst c
    exact ((hPlusMono.1.2 a ha.1 a).2).mpr rfl) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro left out a b c hl hProd ha hb hc
    obtain ⟨v,hv,hOut⟩ := (hLaws.2 s t q left out hCons).mp hProd
    obtain ⟨b0,hb0⟩ := exists_length (ConstructionProbeRaw.cons_raw hCons).1
    obtain ⟨c0,hc0⟩ := exists_length (ConstructionProbeRaw.cons_raw hOut).1
    have hPrev := (he t).mp ih left v a b0 c0 hl hv ha hb0 hc0
    have hBSucc := cons_length hM hw hCons hb0 hb
    have hCSucc := cons_length hM hw hOut hc0 hc
    exact (hAdd a b c).mpr ⟨ha.1,hb.1,(ZF.ordinalAddition_successor_iff hZF (KuratowskiZF.interpretation hM)
      (hw.members_areOrdinals hZF b0 hb0.1) hBSucc).mpr ⟨c0,((hAdd a b0 c0).mp hPrev).2.2,hCSucc⟩⟩)
  exact (he right).mp (hAll right (length_raw hb)) left out a b c hl hp ha hb hc

end PPAC.Migration.ConstructionMergerWordLength
