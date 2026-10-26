/- Pinned ProbeGates.Word head/Gate and gate_of_suffix_intersection.
The source Option head is represented by its exact none/some relations on the
already constructed internal Raw carrier. Gate uses the proved equivalence
old(g) | z iff HeadDiv g z; gate_iff_old_cone records the literal source contract.
No existence of gates or conditional joins is assumed by the head lemmas. -/
import PPAC.Migration.ConstructionProbeOldEmbeddingSyntax

namespace PPAC.Migration.ConstructionProbeGates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeLetterAction (LetterAct)
open ConstructionProbeOldEmbedding
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet InCone)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def HeadNone (zero D q : M.Carrier .set) : Prop := ∃ x, Old zero D x q

def HeadSome (w D S q s : M.Carrier .set) : Prop := ∃ t, Cons w D S s t q

theorem old_no_head {w D S zero x q s : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : Old zero D x q) : ¬ HeadSome w D S q s := by
  rintro ⟨t,ht⟩
  exact old_ne_cons hz hq ht

theorem head_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S q s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : HeadSome w D S q s) (ht : HeadSome w D S q t) : s = t := by
  obtain ⟨v,hv⟩ := hs
  obtain ⟨z,hz⟩ := ht
  exact (cons_injective hM hw hv hz).1

theorem head_partition (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hq : Raw w D S q) :
    HeadNone zero D q ∨ ∃ s, HeadSome w D S q s := by
  rcases cases_raw hM hw hz hzw hq with ⟨x,hx⟩ | ⟨s,t,ht⟩
  · exact Or.inl ⟨x,hx⟩
  · exact Or.inr ⟨s,t,ht⟩

theorem head_none_iff_no_some (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hq : Raw w D S q) :
    HeadNone zero D q ↔ ¬ ∃ s, HeadSome w D S q s := by
  constructor
  · rintro ⟨x,hx⟩ ⟨s,hs⟩
    exact old_no_head hz hx hs
  · intro hn
    exact (head_partition hM hw hz hzw hq).resolve_right hn

theorem head_some_cons_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S mul A b W zero q s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    HeadSome w D S q s ↔ ∃ t, (Project.FirstOrderSemantics.reduct M).mem t W ∧
      ¬ HeadDiv w D S zero mul A b t ∧ Cons w D S s t q := by
  constructor
  · rintro ⟨t,ht⟩
    have hred := (ConstructionProbeReduced.reduced_cons hM hw hz hzw ht).mp ((hW q).mp hq)
    exact ⟨t,(hW t).mpr hred.1,hred.2,ht⟩
  · rintro ⟨t,_,_,ht⟩
    exact ⟨t,ht⟩

theorem headDiv_of_head_eq_some (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A x q s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : HeadSome w D S q s) : HeadDiv w D S zero mul A x q ↔ InCone S A x s := by
  obtain ⟨t,ht⟩ := hq
  exact headDiv_cons_iff hM hw hz ht

theorem headDiv_of_same_head (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A x q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : HeadSome w D S q s) (hr : HeadSome w D S r s) :
    HeadDiv w D S zero mul A x q ↔ HeadDiv w D S zero mul A x r :=
  (headDiv_of_head_eq_some hM hw hz hq).trans (headDiv_of_head_eq_some hM hw hz hr).symm

theorem head_oldAct_exit_ne (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A E e I s z v q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hAlpha : Alphabet D mul e S I A E)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hzE : PureKuratowski.PairMember M s z E)
    (hact : OldAct w D S zero mul A z v q) : ¬ HeadSome w D S q s := by
  rintro ⟨t,ht⟩
  exact ConstructionProbeLetterAction.oldAct_exit_ne_cons hM hw hz hzw hAlpha hs hzE hact ht

theorem head_letterAct_ne_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I s q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hAlpha : Alphabet D mul e S I A E)
    (hact : LetterAct w D S zero mul A b W E s q r) :
    ¬ HeadSome w D S r s ↔ HeadDiv w D S zero mul A b q := by
  rcases hact.2.2 with ⟨hHead,v,z,_,hzE,hzact⟩ | ⟨hn,hcons⟩
  · exact ⟨fun _ => hHead,fun _ => head_oldAct_exit_ne hM hw hz hzw hAlpha hact.1 hzE hzact⟩
  · exact ⟨fun h => (h ⟨q,hcons⟩).elim,fun h => (hn h).elim⟩

/-- Relational form of the source Gate, on every element of the Word carrier. -/
def Gate (w D S zero mul A W G q s g : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z W →
  ((Divides W G q z ∧ ¬ HeadSome w D S z s) ↔ HeadDiv w D S zero mul A g z)

theorem gate_iff_old_cone (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G q s g og : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hog : Old zero D g og) :
    Gate w D S zero mul A W G q s g ↔ ∀ z, (Project.FirstOrderSemantics.reduct M).mem z W →
      ((Divides W G q z ∧ ¬ HeadSome w D S z s) ↔ Divides W G og z) := by
  unfold Gate
  exact forall_congr' (fun z => forall_congr' (fun hzv => iff_congr Iff.rfl
    (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hog hzv).symm))

theorem gate_head_ne {w D S zero mul A W G q s g z : M.Carrier .set}
    (hGate : Gate w D S zero mul A W G q s g)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z W)
    (hgz : HeadDiv w D S zero mul A g z) : ¬ HeadSome w D S z s :=
  ((hGate z hz).mpr hgz).2

theorem gate_dvd_old_iff {w D S zero mul A W G q s g y oy : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hGate : Gate w D S zero mul A W G q s g) (hy : Old zero D y oy)
    (hoy : (Project.FirstOrderSemantics.reduct M).mem oy W) :
    Divides W G q oy ↔ Divides D mul g y := by
  constructor
  · intro h
    exact (headDiv_old_iff hz hy).mp ((hGate oy hoy).mp ⟨h,old_no_head hz hy⟩)
  · intro h
    exact ((hGate oy hoy).mpr ((headDiv_old_iff hz hy).mpr h)).1

theorem gate_old_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W G q s g x z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hGate : Gate w D S zero mul A W G q s g) (hq : HeadSome w D S q s)
    (hx : ¬ HeadDiv w D S zero mul A x q)
    (hzv : (Project.FirstOrderSemantics.reduct M).mem z W) :
    (HeadDiv w D S zero mul A x z ∧ Divides W G q z) ↔
      (HeadDiv w D S zero mul A x z ∧ HeadDiv w D S zero mul A g z) := by
  constructor
  · rintro ⟨hxz,hqz⟩
    refine ⟨hxz,(hGate z hzv).mp ⟨hqz,?_⟩⟩
    intro hs
    exact hx ((headDiv_of_same_head hM hw hz hq hs).mpr hxz)
  · rintro ⟨hxz,hgz⟩
    exact ⟨hxz,((hGate z hzv).mpr hgz).1⟩

/-- Divisibility composition used by the literal suffix-intersection argument. -/
theorem divides_trans {W G unit x y z : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hx : (Project.FirstOrderSemantics.reduct M).mem x W)
    (hxy : Divides W G x y) (hyz : Divides W G y z) : Divides W G x z := by
  obtain ⟨a,ha,hxa⟩ := hxy
  obtain ⟨b,hb,hyb⟩ := hyz
  obtain ⟨ab,hab,hp⟩ := (hm.2.1 a ha).1 b hb
  exact ⟨ab,hab,(hm.2.2 x a b y ab z hx ha hb hxa hp).mp hyb⟩

/-- Source gate_of_suffix_intersection: compute the gate as exit(s)*u,
from the actual suffix/old-b intersection b*u, rather than assume a gate. -/
theorem gate_of_suffix_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s Y q u j ex g : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hCons : Cons w D S s Y q) (hY : (Project.FirstOrderSemantics.reduct M).mem Y W)
    (hnot : ¬ HeadDiv w D S zero mul A b Y)
    (hu : (Project.FirstOrderSemantics.reduct M).mem u D) (hbu : Product mul b u j)
    (hex : PureKuratowski.PairMember M s ex E) (hgu : Product mul ex u g)
    (hInt : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z W →
      ((Divides W G Y z ∧ HeadDiv w D S zero mul A b z) ↔ HeadDiv w D S zero mul A j z)) :
    Gate w D S zero mul A W G q s g := by
  have hs := cons_letter hCons
  have hexD := hAlpha.2.2.2.1.2 s ex hex
  have hjD := ConstructionProbeTransitions.product_closed hm hb hu hbu
  have hgD := ConstructionProbeTransitions.product_closed hm hexD hu hgu
  have hqW := (hW q).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mpr ⟨(hW Y).mp hY,hnot⟩)
  intro z hzW
  constructor
  · rintro ⟨⟨v,hv,hqv⟩,hhead⟩
    obtain ⟨yv,hYv,hletter⟩ := (ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hm hAlpha hW hb hCons).mp ((hG q v z).mp hqv).2
    have hyvW := ConstructionProbeEvaluation.eval_word hM hYv
    have hbyv := (head_letterAct_ne_iff hM hw hz hzw hAlpha hletter).mp hhead
    have hjyv := (hInt yv hyvW).mp ⟨⟨v,hv,(hG Y v yv).mpr ⟨hY,hYv⟩⟩,hbyv⟩
    obtain ⟨k,hk,hjk⟩ := (ConstructionProbeWord.headDiv_iff hM hw hz hzw hW hjD hyvW).mp hjyv
    obtain ⟨uk,huk⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hu (word_raw hW hk)
    have hukW := (hW uk).mpr ((ConstructionProbeReduced.reduced_oldAct hM hw hz hzw huk).mpr ((hW k).mp hk))
    obtain ⟨buk,hbuk⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hb (word_raw hW hukW)
    have he := oldAct_unique hM hw hz hm hAlpha.2.1 (oldAct_mul hM hw hz hm hAlpha.2.2.1 hbu huk hbuk) hjk
    subst buk
    have hexuk := (ConstructionProbeLetterAction.letterAct_oldAct_b hM hw hz hzw hm hAlpha hW hs hukW hbuk hex).mp hletter
    exact (ConstructionProbeRawAction.headDiv_iff hM hw hz hzw hgD).mpr
      ⟨k,word_raw hW hk,oldAct_mul hM hw hz hm hAlpha.2.2.1 hgu huk hexuk⟩
  · intro hgz
    obtain ⟨oj,hoj⟩ := exists_old hM (zero := zero) hjD
    obtain ⟨ou,hou⟩ := exists_old hM (zero := zero) hu
    obtain ⟨og,hog⟩ := exists_old hM (zero := zero) hgD
    have hojW := old_word hM hz hzw hW hoj
    have houW := old_word hM hz hzw hW hou
    have hjj : HeadDiv w D S zero mul A j oj :=
      (headDiv_old_iff hz hoj).mpr ⟨e,hm.1.1,((hm.1.2 j hjD j).2).mpr rfl⟩
    obtain ⟨v,hv,hYv⟩ := ((hInt oj hojW).mpr hjj).1
    have hba : OldAct w D S zero mul A b ou oj := ⟨hb,Or.inl ⟨u,j,hou,hbu,hoj⟩⟩
    have hea : OldAct w D S zero mul A ex ou og := ⟨hexD,Or.inl ⟨u,g,hou,hgu,hog⟩⟩
    have hletter := (ConstructionProbeLetterAction.letterAct_oldAct_b hM hw hz hzw hm hAlpha hW hs houW hba hex).mpr hea
    have hqog : Divides W G q og := ⟨v,hv,(hG q v og).mpr ⟨hqW,
      (ConstructionProbeEvaluation.eval_cons_iff hM hw hz hzw hm hAlpha hW hb hCons).mpr
        ⟨oj,((hG Y v oj).mp hYv).2,hletter⟩⟩⟩
    have hogz := (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hog hzW).mpr hgz
    refine ⟨divides_trans (ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG) hqW hqog hogz,?_⟩
    obtain ⟨k,hk,hgk⟩ := (ConstructionProbeWord.headDiv_iff hM hw hz hzw hW hgD hzW).mp hgz
    obtain ⟨uk,huk⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hu (word_raw hW hk)
    have hukW := (hW uk).mpr ((ConstructionProbeReduced.reduced_oldAct hM hw hz hzw huk).mpr ((hW k).mp hk))
    obtain ⟨euk,heuk⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hexD (word_raw hW hukW)
    have he := oldAct_unique hM hw hz hm hAlpha.2.1 (oldAct_mul hM hw hz hm hAlpha.2.2.1 hgu huk heuk) hgk
    subst euk
    exact head_oldAct_exit_ne hM hw hz hzw hAlpha hs hex heuk

def HeadLaws (w D S zero mul A b W E : M.Carrier .set) : Prop :=
  (∀ q, Raw w D S q → (HeadNone zero D q ↔ ¬ ∃ s, HeadSome w D S q s)) ∧
  (∀ q s t, HeadSome w D S q s → HeadSome w D S q t → s = t) ∧
  (∀ q s, (Project.FirstOrderSemantics.reduct M).mem q W →
    (HeadSome w D S q s ↔ ∃ t, (Project.FirstOrderSemantics.reduct M).mem t W ∧
      ¬ HeadDiv w D S zero mul A b t ∧ Cons w D S s t q)) ∧
  (∀ x q s, HeadSome w D S q s → (HeadDiv w D S zero mul A x q ↔ InCone S A x s)) ∧
  (∀ s q r, LetterAct w D S zero mul A b W E s q r →
    (¬ HeadSome w D S r s ↔ HeadDiv w D S zero mul A b q))

theorem head_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hAlpha : Alphabet D mul e S I A E) (hW : WordCarrier w D S mul A b W) :
    HeadLaws w D S zero mul A b W E :=
  ⟨fun _ hq => head_none_iff_no_some hM hw hz hzw hq,
    fun _ _ _ hs ht => head_unique hM hw hs ht,
    fun _ _ hq => head_some_cons_iff hM hw hz hzw hW hq,
    fun _ _ _ hq => headDiv_of_head_eq_some hM hw hz hq,
    fun _ _ _ hact => head_letterAct_ne_iff hM hw hz hzw hAlpha hact⟩

def GateLaws (w D S zero mul A W G : M.Carrier .set) : Prop :=
  (∀ q s g z, Gate w D S zero mul A W G q s g →
    (Project.FirstOrderSemantics.reduct M).mem z W → HeadDiv w D S zero mul A g z → ¬ HeadSome w D S z s) ∧
  (∀ q s g y oy, Gate w D S zero mul A W G q s g → Old zero D y oy →
    (Project.FirstOrderSemantics.reduct M).mem oy W → (Divides W G q oy ↔ Divides D mul g y)) ∧
  (∀ q s g x z, Gate w D S zero mul A W G q s g → HeadSome w D S q s →
    ¬ HeadDiv w D S zero mul A x q → (Project.FirstOrderSemantics.reduct M).mem z W →
    ((HeadDiv w D S zero mul A x z ∧ Divides W G q z) ↔
      (HeadDiv w D S zero mul A x z ∧ HeadDiv w D S zero mul A g z)))

theorem gate_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W G : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero) : GateLaws w D S zero mul A W G :=
  ⟨fun _ _ _ _ hg hzv hgz => gate_head_ne hg hzv hgz,
    fun _ _ _ _ _ hg hy hoy => gate_dvd_old_iff hz hg hy hoy,
    fun _ _ _ _ _ hg hq hx hzv => gate_old_intersection hM hw hz hg hq hx hzv⟩

end PPAC.Migration.ConstructionProbeGates
