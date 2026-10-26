/- Pinned ProbeWords.Word.letterAct: its two source branches, exact front
reduction, equivariance and injectivity from the existing separated alphabet. -/
import PPAC.Migration.ConstructionProbeWordQuotient

namespace PPAC.Migration.ConstructionProbeLetterAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction
open ConstructionProbeReduced (reduced_oldAct reduced_cons)
open ConstructionProbeWord (WordCarrier word_raw wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeRawActionSyntax (oldAct oldAct_freeClosed oldAct_semantics headDiv headDiv_freeClosed headDiv_semantics)
open ConstructionProbeWordQuotient
open ConstructionProbeAlphabet (Alphabet alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeAction (projected_range projected_indices)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def LetterAct (w D S zero mul A b W E s q r : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem s S ∧
  (Project.FirstOrderSemantics.reduct M).mem q W ∧
  ((HeadDiv w D S zero mul A b q ∧ ∃ v z,
    QuotientValue w D S zero mul A W b q v ∧ PureKuratowski.PairMember M s z E ∧
      OldAct w D S zero mul A z v r) ∨
    (¬ HeadDiv w D S zero mul A b q ∧ Cons w D S s q r))

theorem letterAct_word (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E s q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (h : LetterAct w D S zero mul A b W E s q r) :
    (Project.FirstOrderSemantics.reduct M).mem r W := by
  rcases h.2.2 with ⟨_,v,z,hv,_,hact⟩ | ⟨hnot,hcons⟩
  · exact (hW r).mpr ((reduced_oldAct hM hw hz hzw hact).mpr ((hW v).mp hv.2.1))
  · exact (hW r).mpr ((reduced_cons hM hw hz hzw hcons).mpr ⟨(hW q).mp h.2.1,hnot⟩)

theorem letterAct_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I s q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    ∃ r, LetterAct w D S zero mul A b W E s q r := by
  by_cases hHead : HeadDiv w D S zero mul A b q
  · obtain ⟨v,hv⟩ := quotient_total hM hw hz hzw hW hb hq hHead
    have hE := hAlpha.2.2.2.1
    obtain ⟨z,hzE,_⟩ := hE.1.2 s hs
    obtain ⟨r,hr⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1
      (hE.2 s z hzE) (word_raw hW hv.2.1)
    exact ⟨r,hs,hq,Or.inl ⟨hHead,v,z,hv,hzE,hr⟩⟩
  · obtain ⟨r,hr⟩ := exists_cons hM hw hs (word_raw hW hq)
    exact ⟨r,hs,hq,Or.inr ⟨hHead,hr⟩⟩

theorem letterAct_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I s q r r' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hr : LetterAct w D S zero mul A b W E s q r)
    (hr' : LetterAct w D S zero mul A b W E s q r') : r = r' := by
  rcases hr.2.2 with ⟨hHead,v,z,hv,hzE,hact⟩ | ⟨hnot,hcons⟩
  · rcases hr'.2.2 with ⟨_,v',z',hv',hzE',hact'⟩ | ⟨hnot,_⟩
    · have he := quotient_unique hM hw hz hm hAlpha.2.2.1 hv hv'
      subst v'
      have he := ForcingConditionGraphs.function_unique hAlpha.2.2.2.1.1 hzE hzE'
      subst z'
      exact oldAct_unique hM hw hz hm hAlpha.2.1 hact hact'
    · exact (hnot hHead).elim
  · rcases hr'.2.2 with ⟨hHead,_⟩ | ⟨_,hcons'⟩
    · exact (hnot hHead).elim
    · exact cons_unique hM hw hcons hcons'

/-- Source letterAct_oldAct_b, including both directions of its value relation. -/
theorem letterAct_oldAct_b (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I s q r z v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hact : OldAct w D S zero mul A b q r) (hzE : PureKuratowski.PairMember M s z E) :
    LetterAct w D S zero mul A b W E s r v ↔ OldAct w D S zero mul A z q v := by
  have hHead : HeadDiv w D S zero mul A b r :=
    (ConstructionProbeRawAction.headDiv_iff hM hw hz hzw hact.1).mpr ⟨q,word_raw hW hq,hact⟩
  have hr : (Project.FirstOrderSemantics.reduct M).mem r W :=
    (hW r).mpr ((reduced_oldAct hM hw hz hzw hact).mpr ((hW q).mp hq))
  constructor
  · rintro ⟨_,_,hLetter⟩
    rcases hLetter with ⟨_,t,z',ht,hzE',htv⟩ | ⟨hnot,_⟩
    · have he := (quotient_oldAct_iff hM hw hz hzw hm hAlpha.2.2.1 hW hq hact).mp ht
      subst t
      have he := ForcingConditionGraphs.function_unique hAlpha.2.2.2.1.1 hzE' hzE
      subst z'
      exact htv
    · exact (hnot hHead).elim
  · intro hv
    exact ⟨hs,hr,Or.inl ⟨hHead,q,z,⟨hr,hq,hact⟩,hzE,hv⟩⟩

/-- Source equivariance: act by a after prepending s, or prepend a.s. -/
theorem oldAct_letterAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I a s t q r v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hletter : Product A a s t)
    (hL : LetterAct w D S zero mul A b W E s q r)
    (hact : OldAct w D S zero mul A a r v) : LetterAct w D S zero mul A b W E t q v := by
  refine ⟨projected_range hAlpha.2.1 hletter,hL.2.1,?_⟩
  rcases hL.2.2 with ⟨hHead,u,z,hu,hzE,hzr⟩ | ⟨hnot,hcons⟩
  · obtain ⟨az,_,haz⟩ := (hm.2.1 a hact.1).1 z (hAlpha.2.2.2.1.2 s z hzE)
    exact Or.inl ⟨hHead,u,az,hu,hAlpha.2.2.2.2.1 a s t z az hletter hzE haz,
      oldAct_mul hM hw hz hm hAlpha.2.2.1 haz hzr hact⟩
  · obtain ⟨_,t',ht',hcons'⟩ := (oldAct_cons_iff hM hw hz hcons).mp hact
    obtain ⟨p,hp,hpt⟩ := hletter
    obtain ⟨p',hp',hpt'⟩ := ht'
    have he := KuratowskiZF.code_unique hM hp hp'
    subst p'
    have he := ForcingConditionGraphs.function_unique hAlpha.2.1.1 hpt' hpt
    subst t'
    exact Or.inr ⟨hnot,hcons'⟩

/-- The exact source separated-alphabet obstruction. -/
theorem not_headDiv_exit_cons (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A E e I s z q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hAlpha : Alphabet D mul e S I A E)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hzE : PureKuratowski.PairMember M s z E) (hcons : Cons w D S s q r) :
    ¬ HeadDiv w D S zero mul A z r := by
  intro hHead
  exact hAlpha.2.2.2.2.2 s z hs hzE ((headDiv_cons_iff hM hw hz hcons).mp hHead)

theorem oldAct_exit_ne_cons (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A E e I s z v q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hAlpha : Alphabet D mul e S I A E)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hzE : PureKuratowski.PairMember M s z E)
    (hact : OldAct w D S zero mul A z v r) (hcons : Cons w D S s q r) : False := by
  apply not_headDiv_exit_cons hM hw hz hAlpha hs hzE hcons
  exact (ConstructionProbeRawAction.headDiv_iff hM hw hz hzw hact.1).mpr
    ⟨v,(oldAct_raw hM hz hzw hact).1,hact⟩

theorem letterAct_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I s q q' r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hq : LetterAct w D S zero mul A b W E s q r)
    (hq' : LetterAct w D S zero mul A b W E s q' r) : q = q' := by
  rcases hq.2.2 with ⟨_,v,z,hv,hzE,hact⟩ | ⟨_,hcons⟩
  · rcases hq'.2.2 with ⟨_,v',z',hv',hzE',hact'⟩ | ⟨_,hcons'⟩
    · have he := ForcingConditionGraphs.function_unique hAlpha.2.2.2.1.1 hzE hzE'
      subst z'
      have he := oldAct_injective hM hw hz hm hAlpha.2.2.1 hact hact'
      subst v'
      exact oldAct_unique hM hw hz hm hAlpha.2.1 (oldAct_quotient hv) (oldAct_quotient hv')
    · exact (oldAct_exit_ne_cons hM hw hz hzw hAlpha hq.1 hzE hact hcons').elim
  · rcases hq'.2.2 with ⟨_,v',z',_,hzE',hact'⟩ | ⟨_,hcons'⟩
    · exact (oldAct_exit_ne_cons hM hw hz hzw hAlpha hq'.1 hzE' hact' hcons).elim
    · exact (cons_injective hM hw hcons hcons').2


def LetterLaws (w D S zero mul A b W E : M.Carrier .set) : Prop :=
  (∀ s q, (Project.FirstOrderSemantics.reduct M).mem s S →
    (Project.FirstOrderSemantics.reduct M).mem q W → ∃ r, LetterAct w D S zero mul A b W E s q r) ∧
  (∀ s q r, LetterAct w D S zero mul A b W E s q r →
    (Project.FirstOrderSemantics.reduct M).mem r W) ∧
  (∀ s q r r', LetterAct w D S zero mul A b W E s q r →
    LetterAct w D S zero mul A b W E s q r' → r = r') ∧
  (∀ s q q' r, LetterAct w D S zero mul A b W E s q r →
    LetterAct w D S zero mul A b W E s q' r → q = q') ∧
  (∀ s q r z v, (Project.FirstOrderSemantics.reduct M).mem s S →
    (Project.FirstOrderSemantics.reduct M).mem q W → OldAct w D S zero mul A b q r →
    PureKuratowski.PairMember M s z E →
    (LetterAct w D S zero mul A b W E s r v ↔ OldAct w D S zero mul A z q v)) ∧
  (∀ a s t q r v, Product A a s t → LetterAct w D S zero mul A b W E s q r →
    OldAct w D S zero mul A a r v → LetterAct w D S zero mul A b W E t q v) ∧
  (∀ s z q r, (Project.FirstOrderSemantics.reduct M).mem s S →
    PureKuratowski.PairMember M s z E → Cons w D S s q r → ¬ HeadDiv w D S zero mul A z r)

theorem letter_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) : LetterLaws w D S zero mul A b W E := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro s q hs hq
    exact letterAct_total hM hw hz hzw hm hAlpha hW hb hs hq
  · intro s q r h
    exact letterAct_word hM hw hz hzw hW h
  · intro s q r r' hr hr'
    exact letterAct_unique hM hw hz hm hAlpha hr hr'
  · intro s q q' r hq hq'
    exact letterAct_injective hM hw hz hzw hm hAlpha hq hq'
  · intro s q r z v hs hq hact hzE
    exact letterAct_oldAct_b hM hw hz hzw hm hAlpha hW hs hq hact hzE
  · intro a s t q r v hletter hL hact
    exact oldAct_letterAct hM hw hz hm hAlpha hletter hL hact
  · intro s z q r hs hzE hcons
    exact not_headDiv_exit_cons hM hw hz hAlpha hs hzE hcons

def letterAct {m : Nat} (w D S zero mul A b W E s q r : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound s) (.bound S)) (.conj (.mem (.bound q) (.bound W)) (.disj (.conj (headDiv w D S zero
    mul A b q) (.existsE (.existsE (.conj (quotientValue w.succ.succ D.succ.succ S.succ.succ zero.succ.succ
    mul.succ.succ A.succ.succ W.succ.succ b.succ.succ q.succ.succ 1) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge E.succ.succ s.succ.succ 0)) (oldAct w.succ.succ D.succ.succ S.succ.succ
    zero.succ.succ mul.succ.succ A.succ.succ 0 1 r.succ.succ)))))) (.conj (.neg (headDiv w D S zero mul A b
    q)) (cons w D S s q r)))))

def letterLaws {m : Nat} (w D S zero mul A b W E : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound S.succ.succ)) (.imp (.mem (.bound 0) (.bound
    W.succ.succ)) (.existsE (letterAct w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ
    zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ W.succ.succ.succ
    E.succ.succ.succ 2 1 0)))))) (.conj (.forallE (.forallE (.forallE (.imp (letterAct w.succ.succ.succ
    D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ
    b.succ.succ.succ W.succ.succ.succ E.succ.succ.succ 2 1 0) (.mem (.bound 0) (.bound
    W.succ.succ.succ)))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (letterAct
    w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ zero.succ.succ.succ.succ
    mul.succ.succ.succ.succ A.succ.succ.succ.succ b.succ.succ.succ.succ W.succ.succ.succ.succ
    E.succ.succ.succ.succ 3 2 1) (.imp (letterAct w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ
    b.succ.succ.succ.succ W.succ.succ.succ.succ E.succ.succ.succ.succ 3 2 0) (Project.Formula.extensionalEq
    (.bound 1) (.bound 0)))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (letterAct
    w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ zero.succ.succ.succ.succ
    mul.succ.succ.succ.succ A.succ.succ.succ.succ b.succ.succ.succ.succ W.succ.succ.succ.succ
    E.succ.succ.succ.succ 3 2 0) (.imp (letterAct w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ
    b.succ.succ.succ.succ W.succ.succ.succ.succ E.succ.succ.succ.succ 3 1 0) (Project.Formula.extensionalEq
    (.bound 2) (.bound 1)))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem
    (.bound 4) (.bound S.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 3) (.bound
    W.succ.succ.succ.succ.succ)) (.imp (oldAct w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ
    A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ 3 2) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge E.succ.succ.succ.succ.succ 4 1)) (.iff (letterAct w.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ
    W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ 4 2 0) (oldAct w.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 1 3 0))))))))))) (.conj (.forallE (.forallE
    (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (letterAct w.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ
    W.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ 4 2 1) (.imp (oldAct
    w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ 5 1
    0) (letterAct w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
    A.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ
    E.succ.succ.succ.succ.succ.succ 3 2 0)))))))))) (.forallE (.forallE (.forallE (.forallE (.imp (.mem
    (.bound 3) (.bound S.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    E.succ.succ.succ.succ 3 2)) (.imp (cons w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ 3 1 0) (.neg (headDiv w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ 2
    0)))))))))))))))

theorem letterAct_freeClosed {m : Nat} (w D S zero mul A b W E s q r : Fin m) :
    (letterAct w D S zero mul A b W E s q r).FreeClosed := by
  simp -implicitDefEqProofs [letterAct,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    headDiv_freeClosed,quotientValue_freeClosed,oldAct_freeClosed,cons_freeClosed]

theorem letterAct_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E s q r : Fin m) :
    Project.Formula.satisfies env (letterAct w D S zero mul A b W E s q r) ↔
      LetterAct (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A)
        (env.bound b) (env.bound W) (env.bound E) (env.bound s) (env.bound q) (env.bound r) := by
  simp only [letterAct,LetterAct,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,headDiv_semantics hM,quotientValue_semantics hM,oldAct_semantics hM,
    cons_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem letterLaws_freeClosed {m : Nat} (w D S zero mul A b W E : Fin m) :
    (letterLaws w D S zero mul A b W E).FreeClosed := by
  simp -implicitDefEqProofs [letterLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    letterAct_freeClosed,oldAct_freeClosed,cons_freeClosed,headDiv_freeClosed,
    Project.Formula.extensionalEq_freeClosed_iff]

theorem letterLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E : Fin m) :
    Project.Formula.satisfies env (letterLaws w D S zero mul A b W E) ↔
      LetterLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A)
        (env.bound b) (env.bound W) (env.bound E) := by
  simp only [letterLaws,LetterLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    letterAct_semantics hM,oldAct_semantics hM,headDiv_semantics hM,cons_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    product_semantics (M := M)]
  rfl

def lawsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isEmpty (.bound 3))
        (.imp (.mem (.bound 3) (.bound 0))
          (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 11) 4 9))
            (.imp (alphabet (1 : Fin 11) 4 9 2 10 5 8)
              (.imp (wordCarrier (0 : Fin 11) 1 2 4 5 6 7)
                (.imp (.mem (.bound 6) (.bound 1)) (letterLaws (0 : Fin 11) 1 2 3 4 5 6 7 8))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
    ProjectSyntax.freeClosed,alphabet_freeClosed,wordCarrier_freeClosed,letterLaws_freeClosed]

theorem laws_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence lawsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) lawsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),alphabet_semantics hM,
    wordCarrier_semantics hM,letterLaws_semantics hM]
  exact fun hw hz hzw hm hAlpha hW hb => letter_laws hM hw hz hzw hm hAlpha hW hb

theorem laws_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence lawsSentence) := ModelTransfer.derives (fun _ hM => laws_models hM)

end PPAC.Migration.ConstructionProbeLetterAction
