/- Pinned ProbeWords.Raw.reduced: every proper tail has a head not divisible
by b. Internal lengths range over all of omega; no host List or Nat recursion. -/
import PPAC.Migration.ConstructionProbeRawAction

namespace PPAC.Migration.ConstructionProbeReduced
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction
open ForcingSupportSize (MapsTo)
open ConstructionProbeAlphabet (InCone)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Head divisibility of the prefix of length n of the reversed letter graph.
The empty prefix has the compulsory terminal x as its head. -/
def PrefixHead (D S mul A b n f x : M.Carrier .set) : Prop :=
  ((∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i n) ∧ Divides D mul b x) ∨
  ∃ k s, (Project.FirstOrderSemantics.reduct M).SuccessorOf n k ∧
    PureKuratowski.PairMember M k s f ∧ InCone S A b s

/-- Only proper prefixes are tested: the highest letter itself is unrestricted. -/
def Good (D S mul A b n f x : M.Carrier .set) : Prop :=
  ∀ k, (Project.FirstOrderSemantics.reduct M).mem k n → ¬ PrefixHead D S mul A b k f x

def Reduced (w D S mul A b q : M.Carrier .set) : Prop := ∃ n f x,
  (Project.FirstOrderSemantics.reduct M).mem n w ∧ MapsTo n S f ∧
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q f x ∧
  Good D S mul A b n f x

theorem reduced_raw {w D S mul A b q : M.Carrier .set} (h : Reduced w D S mul A b q) :
    Raw w D S q := by
  obtain ⟨n,f,x,hn,hf,hx,hq,_⟩ := h
  exact ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩

/-- The same internal word has the same sequence, terminal and length. -/
theorem reduced_iff_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S mul A b q n f x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hf : MapsTo n S f)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hq : PureKuratowski.Code M q f x) :
    Reduced w D S mul A b q ↔ Good D S mul A b n f x := by
  constructor
  · rintro ⟨m,g,y,hm,hg,_,hq',hGood⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    have hZF := ModelTransfer.project_models_iff.mp hM
    have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (native_sequence hM (hw.members_areOrdinals hZF n hn) hf)
      (native_sequence hM (hw.members_areOrdinals hZF m hm) hg)
    subst m
    exact hGood
  · intro hGood
    exact ⟨n,f,x,hn,hf,hx,hq,hGood⟩

/-- The coordinate test is exactly the source Raw.headDiv on an actual prefix. -/
theorem prefixHead_iff_headDiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b q n f x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hf : MapsTo n S f)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hq : PureKuratowski.Code M q f x) :
    PrefixHead D S mul A b n f x ↔ HeadDiv w D S zero mul A b q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hseq := native_sequence hM (hw.members_areOrdinals hZF n hn) hf
  constructor
  · rintro (⟨hempty,hdiv⟩ | ⟨k,s,hSucc,hs,hCone⟩)
    · have he : f = zero := SetTheory.Structure.IsFiniteSequenceOfLength.empty_sequence_unique
        hZF.1 ⟨hn,hseq⟩
        ⟨hzw,SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz⟩ hempty hz
      subst f
      exact Or.inl ⟨x,⟨hx,hq⟩,hdiv⟩
    · have hk : (Project.FirstOrderSemantics.reduct M).mem k w :=
        (hw.isOrdinal hZF).transitive n hn k hSucc.predecessor_mem
      obtain ⟨g,hRestriction⟩ := ZF.exists_restriction hZF (KuratowskiZF.interpretation hM) f k
      have hgSeq := SetTheory.Structure.IsSequenceOfLength.restriction hseq hSucc.predecessor_mem hRestriction
      have hg : MapsTo k S g := maps_of_sequence hM hgSeq
        (fun i y hy => hf.2 i y ((hRestriction.2 i y).mp hy).2)
      obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM g x
      have hd : (Project.FirstOrderSemantics.reduct M).IsFiniteSequenceLastDecomposition
          (KuratowskiZF.interpretation hM) w f n k g s :=
        ⟨⟨hn,hseq⟩,hk,hSucc,⟨hk,hgSeq⟩,hRestriction,hs⟩
      exact Or.inr ⟨s,t,⟨k,n,g,f,x,hk,hn,hSucc,hg,hf,hx,hf.2 k s hs,ht,hq,
        decomposition_append hM hf hd⟩,hCone⟩
  · rintro (⟨y,hOld,hdiv⟩ | ⟨s,t,hCons,hCone⟩)
    · obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hOld.2
      refine Or.inl ⟨?_,hdiv⟩
      intro i hi
      obtain ⟨y,hy⟩ := (hseq.2.2 i).mp hi
      obtain ⟨p,_,hp⟩ := hy
      exact hz p hp
    · obtain ⟨k,m,g,g',y,hk,hm,hSucc,hg,hg',_,_,_,hq',happend⟩ := hCons
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
      have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1 hseq
        (native_sequence hM (hw.members_areOrdinals hZF m hm) hg')
      subst m
      exact Or.inr ⟨k,s,hSucc,(happend k s).mpr (Or.inr ⟨rfl,rfl⟩),hCone⟩

/-- Appending the new highest letter cannot change any proper-prefix head. -/
theorem prefixHead_append_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D S mul A b n m f g x a k : M.Carrier .set}
    (hn : (Project.FirstOrderSemantics.reduct M).IsOrdinal n)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k m)
    (happend : ∀ i y, PureKuratowski.PairMember M i y g ↔
      PureKuratowski.PairMember M i y f ∨ (i = n ∧ y = a)) :
    PrefixHead D S mul A b k g x ↔ PrefixHead D S mul A b k f x := by
  constructor
  · rintro (hEmpty | ⟨j,s,hkj,hs,hCone⟩)
    · exact Or.inl hEmpty
    · rcases (happend j s).mp hs with hs | ⟨he,_⟩
      · exact Or.inr ⟨j,s,hkj,hs,hCone⟩
      · subst j
        have hnk := hkj.predecessor_mem
        rcases (hSucc k).mp hk with hkn | heq
        · have hnn := hn.transitive k hkn n hnk
          exact (hn.wellOrder.linear.irrefl n hnn hnn).elim
        · have he : k = n := (ModelTransfer.extensionality hM).eq_of_same_members k n heq
          subst k
          exact (hn.wellOrder.linear.irrefl n hnk hnk).elim
  · rintro (hEmpty | ⟨j,s,hkj,hs,hCone⟩)
    · exact Or.inl hEmpty
    · exact Or.inr ⟨j,s,hkj,(happend j s).mpr (Or.inl hs),hCone⟩

theorem good_append_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D S mul A b n m f g x a : M.Carrier .set}
    (hn : (Project.FirstOrderSemantics.reduct M).IsOrdinal n)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf m n)
    (happend : ∀ i y, PureKuratowski.PairMember M i y g ↔
      PureKuratowski.PairMember M i y f ∨ (i = n ∧ y = a)) :
    Good D S mul A b m g x ↔ Good D S mul A b n f x ∧ ¬ PrefixHead D S mul A b n f x := by
  constructor
  · intro hGood
    constructor
    · intro k hk hHead
      have hkm := (hSucc k).mpr (Or.inl hk)
      exact hGood k hkm ((prefixHead_append_iff hM hn hSucc hkm happend).mpr hHead)
    · intro hHead
      exact hGood n hSucc.predecessor_mem
        ((prefixHead_append_iff hM hn hSucc hSucc.predecessor_mem happend).mpr hHead)
  · rintro ⟨hGood,hLast⟩ k hk hHead
    have hHead' := (prefixHead_append_iff hM hn hSucc hk happend).mp hHead
    rcases (hSucc k).mp hk with hk | heq
    · exact hGood k hk hHead'
    · have he : k = n := (ModelTransfer.extensionality hM).eq_of_same_members k n heq
      subst k
      exact hLast hHead'

theorem reduced_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b x q : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hq : Old zero D x q) :
    Reduced w D S mul A b q := by
  have hf : MapsTo zero S zero := maps_of_sequence hM
    (SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)
    (by intro i y h; obtain ⟨p,_,hp⟩ := h; exact (hz p hp).elim)
  exact ⟨zero,zero,x,hzw,hf,hq.1,hq.2,fun k hk => (hz k hk).elim⟩

theorem reduced_cons (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b s t q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hq : Cons w D S s t q) :
    Reduced w D S mul A b q ↔
      Reduced w D S mul A b t ∧ ¬ HeadDiv w D S zero mul A b t := by
  obtain ⟨n,m,f,g,x,hn,hm,hSucc,hf,hg,hx,_,ht,hq,happend⟩ := hq
  rw [reduced_iff_at hM hw hm hg hx hq,reduced_iff_at hM hw hn hf hx ht]
  exact (good_append_iff hM (hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) n hn)
    hSucc happend).trans (and_congr Iff.rfl (not_congr (prefixHead_iff_headDiv hM hw hz hzw hn hf hx ht)))

theorem reduced_oldAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b a q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (h : OldAct w D S zero mul A a q r) :
    Reduced w D S mul A b r ↔ Reduced w D S mul A b q := by
  rcases h.2 with ⟨x,y,hq,_,hr⟩ | ⟨s,t,v,hq,_,hr⟩
  · exact ⟨fun _ => reduced_old hM hz hzw hq,fun _ => reduced_old hM hz hzw hr⟩
  · exact (reduced_cons hM hw hz hzw hr).trans (reduced_cons hM hw hz hzw hq).symm


def prefixHead {m : Nat} (D S mul A b n f x : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (.forallE (.neg (.mem (.bound 0) (.bound n.succ)))) (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides D mul b x))) (.existsE (.existsE (.conj (Project.Formula.isSuccessor
    (.bound n.succ.succ) (.bound 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1
    0)) (ConstructionProbeAlphabet.inCone S.succ.succ A.succ.succ b.succ.succ 0))))))

def good {m : Nat} (D S mul A b n f x : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound n.succ)) (.neg (prefixHead D.succ S.succ mul.succ A.succ b.succ 0
    f.succ x.succ))))

def reduced {m : Nat} (w D S mul A b q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound w.succ.succ.succ)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 1 2 S.succ.succ.succ)) (.conj (.mem (.bound 0)
    (.bound D.succ.succ.succ)) (.conj (ProjectSyntax.encode id (PairSyntax.ordered q.succ.succ.succ 1 0))
    (good D.succ.succ.succ S.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ 2 1
    0))))))))

theorem prefixHead_freeClosed {m : Nat} (D S mul A b n f x : Fin m) :
    (prefixHead D S mul A b n f x).FreeClosed := by
  simp -implicitDefEqProofs [prefixHead,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isSuccessor,Project.Formula.extensionalEq_freeClosed_iff,
    ConstructionProbeAlphabet.inCone_freeClosed]

theorem good_freeClosed {m : Nat} (D S mul A b n f x : Fin m) :
    (good D S mul A b n f x).FreeClosed := by
  simp -implicitDefEqProofs [good,Definitional.Formula.FreeClosed,prefixHead_freeClosed]

theorem reduced_freeClosed {m : Nat} (w D S mul A b q : Fin m) :
    (reduced w D S mul A b q).FreeClosed := by
  simp -implicitDefEqProofs [reduced,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,good_freeClosed]

theorem prefixHead_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S mul A b n f x : Fin m) :
    Project.Formula.satisfies env (prefixHead D S mul A b n f x) ↔
      PrefixHead (env.bound D) (env.bound S) (env.bound mul) (env.bound A)
        (env.bound b) (env.bound n) (env.bound f) (env.bound x) := by
  simp only [prefixHead,PrefixHead,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isSuccessor_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionProbeAlphabet.inCone_semantics hM]
  rfl

theorem good_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S mul A b n f x : Fin m) :
    Project.Formula.satisfies env (good D S mul A b n f x) ↔
      Good (env.bound D) (env.bound S) (env.bound mul) (env.bound A)
        (env.bound b) (env.bound n) (env.bound f) (env.bound x) := by
  simp only [good,Good,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_neg_iff,
    prefixHead_semantics hM]
  rfl

theorem reduced_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S mul A b q : Fin m) :
    Project.Formula.satisfies env (reduced w D S mul A b q) ↔
      Reduced (env.bound w) (env.bound D) (env.bound S) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound q) := by
  simp only [reduced,Reduced,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_code,good_semantics hM]
  rfl

end PPAC.Migration.ConstructionProbeReduced
