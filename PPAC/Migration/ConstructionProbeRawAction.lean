/- Pinned ProbeWords.Raw.oldAct/headDiv. Only the first constructor is changed;
   the tail remains exactly the original internal word. -/
import PPAC.Migration.ConstructionProbeRaw
import PPAC.Migration.ConstructionProbeAlphabet

namespace PPAC.Migration.ConstructionProbeRawAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (ActionLaws projected projected_indices projected_range)
open ConstructionProbeAlphabet (InCone)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def OldAct (w D S zero mul A b q r : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem b D ∧
  ((∃ x y, Old zero D x q ∧ Product mul b x y ∧ Old zero D y r) ∨
    ∃ s t v, Cons w D S s t q ∧ Product A b s v ∧ Cons w D S v t r)

def HeadDiv (w D S zero mul A b q : M.Carrier .set) : Prop :=
  (∃ x, Old zero D x q ∧ Divides D mul b x) ∨
    ∃ s t, Cons w D S s t q ∧ InCone S A b s

theorem cons_letter {w D S s t q : M.Carrier .set} (h : Cons w D S s t q) :
    (Project.FirstOrderSemantics.reduct M).mem s S := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hs,_⟩ := h
  exact hs

theorem oldAct_raw (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b q r : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (h : OldAct w D S zero mul A b q r) : Raw w D S q ∧ Raw w D S r := by
  rcases h.2 with ⟨x,y,hq,_,hr⟩ | ⟨s,t,v,hq,_,hr⟩
  · exact ⟨old_raw hM hz hzw hq,old_raw hM hz hzw hr⟩
  · exact ⟨(cons_raw hq).2,(cons_raw hr).2⟩

theorem oldAct_old_iff {w D S zero mul A b x q r : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : Old zero D x q) : OldAct w D S zero mul A b q r ↔
      (Project.FirstOrderSemantics.reduct M).mem b D ∧ ∃ y, Product mul b x y ∧ Old zero D y r := by
  constructor
  · rintro ⟨hb,h⟩
    rcases h with ⟨x',y,hq',hxy,hr⟩ | ⟨s,t,v,hq',_,_⟩
    · have he := old_injective hq hq'
      subst x'
      exact ⟨hb,y,hxy,hr⟩
    · exact (old_ne_cons hz hq hq').elim
  · rintro ⟨hb,y,hxy,hr⟩
    exact ⟨hb,Or.inl ⟨x,y,hq,hxy,hr⟩⟩

theorem oldAct_cons_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b s t q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : Cons w D S s t q) : OldAct w D S zero mul A b q r ↔
      (Project.FirstOrderSemantics.reduct M).mem b D ∧ ∃ v, Product A b s v ∧ Cons w D S v t r := by
  constructor
  · rintro ⟨hb,h⟩
    rcases h with ⟨x,y,hq',_,_⟩ | ⟨s',t',v,hq',hsv,hr⟩
    · exact (old_ne_cons hz hq' hq).elim
    · obtain ⟨rfl,rfl⟩ := cons_injective hM hw hq hq'
      exact ⟨hb,v,hsv,hr⟩
  · rintro ⟨hb,v,hsv,hr⟩
    exact ⟨hb,Or.inr ⟨s,t,v,hq,hsv,hr⟩⟩

theorem oldAct_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e I b q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hI : Representatives D S I) (hA : MapsTo I S A)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hq : Raw w D S q) :
    ∃ r, OldAct w D S zero mul A b q r := by
  rcases cases_raw hM hw hz hzw hq with ⟨x,hx⟩ | ⟨s,t,hst⟩
  · obtain ⟨y,hy,hxy⟩ := (hm.2.1 b hb).1 x hx.1
    obtain ⟨r,hr⟩ := exists_old hM hy
    exact ⟨r,hb,Or.inl ⟨x,y,hx,hxy,hr⟩⟩
  · obtain ⟨v,hv,hsv⟩ := projected hM hI hA hb (cons_letter hst)
    obtain ⟨r,hr⟩ := exists_cons hM hw hv (cons_raw hst).1
    exact ⟨r,hb,Or.inr ⟨s,t,v,hst,hsv,hr⟩⟩

theorem oldAct_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e I b q r r' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (hA : MapsTo I S A)
    (hr : OldAct w D S zero mul A b q r) (hr' : OldAct w D S zero mul A b q r') : r = r' := by
  rcases hr with ⟨hb,⟨x,y,hq,hxy,hyr⟩ | ⟨s,t,v,hq,hsv,hvr⟩⟩
  · obtain ⟨_,y',hxy',hyr'⟩ := (oldAct_old_iff hz hq).mp hr'
    have he := (hm.2.1 b hb).2.1 x y y' hq.1 hxy hxy'
    subst y'
    exact old_unique hM hyr hyr'
  · obtain ⟨_,v',hsv',hvr'⟩ := (oldAct_cons_iff hM hw hz hq).mp hr'
    obtain ⟨p,hp,hpv⟩ := hsv
    obtain ⟨p',hp',hpv'⟩ := hsv'
    have he := KuratowskiZF.code_unique hM hp hp'
    subst p'
    have he := ForcingConditionGraphs.function_unique hA.1 hpv hpv'
    subst v'
    exact cons_unique hM hw hvr hvr'

theorem oldAct_one (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (ha : ActionLaws mul e S A) (hq : Raw w D S q) :
    OldAct w D S zero mul A e q q := by
  refine ⟨hm.1.1,?_⟩
  rcases cases_raw hM hw hz hzw hq with ⟨x,hx⟩ | ⟨s,t,hs⟩
  · exact Or.inl ⟨x,x,hx,((hm.1.2 x hx.1 x).1).mpr rfl,hx⟩
  · exact Or.inr ⟨s,t,s,hs,ha.1 s (cons_letter hs),hs⟩

theorem oldAct_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e b a ba q r v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (ha : ActionLaws mul e S A)
    (hba : Product mul b a ba) (har : OldAct w D S zero mul A a q r)
    (hbv : OldAct w D S zero mul A b r v) : OldAct w D S zero mul A ba q v := by
  have hb := hbv.1
  have haD := har.1
  refine ⟨ConstructionProbeTransitions.product_closed hm hb haD hba,?_⟩
  rcases har.2 with ⟨x,y,hx,haxy,hy⟩ | ⟨s,t,z,hs,hasz,hzrt⟩
  · obtain ⟨_,z,hbyz,hzv⟩ := (oldAct_old_iff hz hy).mp hbv
    exact Or.inl ⟨x,z,hx,(hm.2.2 b a x ba y z hb haD hx.1 hba haxy).mpr hbyz,hzv⟩
  · obtain ⟨_,z',hbzz',hz'v⟩ := (oldAct_cons_iff hM hw hz hzrt).mp hbv
    exact Or.inr ⟨s,t,z',hs,ha.2.1 b a ba s z z' hba hasz hbzz',hz'v⟩

theorem oldAct_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e b q r v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (ha : ActionLaws mul e S A)
    (hq : OldAct w D S zero mul A b q v) (hr : OldAct w D S zero mul A b r v) : q = r := by
  have hb := hq.1
  rcases hq.2 with ⟨x,y,hx,hbxy,hy⟩ | ⟨s,t,z,hs,hbsz,hzv⟩
  · rcases hr.2 with ⟨x',y',hx',hbx'y',hy'⟩ | ⟨s',t',z',_,_,hz'v⟩
    · have he := old_injective hy hy'
      subst y'
      have he := (hm.2.1 b hb).2.2 x x' y hx.1 hx'.1 hbxy hbx'y'
      subst x'
      exact old_unique hM hx hx'
    · exact (old_ne_cons hz hy hz'v).elim
  · rcases hr.2 with ⟨x',y',_,_,hy'⟩ | ⟨s',t',z',hs',hbs'z',hz'v⟩
    · exact (old_ne_cons hz hy' hzv).elim
    · obtain ⟨rfl,rfl⟩ := cons_injective hM hw hzv hz'v
      have he := ha.2.2 b s s' z hbsz hbs'z'
      subst s'
      exact cons_unique hM hw hs hs'

theorem headDiv_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) :
    HeadDiv w D S zero mul A b q ↔ ∃ r, Raw w D S r ∧ OldAct w D S zero mul A b r q := by
  constructor
  · rintro (⟨x,hx,y,hy,hbyx⟩ | ⟨s,t,hst,v,hv,hbvs⟩)
    · obtain ⟨r,hr⟩ := exists_old hM hy
      exact ⟨r,old_raw hM hz hzw hr,hb,Or.inl ⟨y,x,hr,hbyx,hx⟩⟩
    · obtain ⟨r,hr⟩ := exists_cons hM hw hv (cons_raw hst).1
      exact ⟨r,(cons_raw hr).2,hb,Or.inr ⟨v,t,s,hr,hbvs,hst⟩⟩
  · rintro ⟨r,_,_,h⟩
    rcases h with ⟨x,y,hx,hbxy,hy⟩ | ⟨s,t,v,hst,hbsv,hvt⟩
    · exact Or.inl ⟨y,hy,x,hx.1,hbxy⟩
    · exact Or.inr ⟨v,t,hvt,s,cons_letter hst,hbsv⟩


theorem headDiv_old_iff {w D S zero mul A b x q : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : Old zero D x q) : HeadDiv w D S zero mul A b q ↔ Divides D mul b x := by
  constructor
  · rintro (⟨y,hy,hdiv⟩ | ⟨s,t,hst,_⟩)
    · have he := old_injective hq hy
      exact he.symm ▸ hdiv
    · exact (old_ne_cons hz hq hst).elim
  · exact fun h => Or.inl ⟨x,hq,h⟩

theorem headDiv_cons_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b s t q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hq : Cons w D S s t q) : HeadDiv w D S zero mul A b q ↔ InCone S A b s := by
  constructor
  · rintro (⟨x,hx,_⟩ | ⟨s',t',hq',hcone⟩)
    · exact (old_ne_cons hz hx hq).elim
    · obtain ⟨rfl,_⟩ := cons_injective hM hw hq hq'
      exact hcone
  · exact fun h => Or.inr ⟨s,t,hq,h⟩

end PPAC.Migration.ConstructionProbeRawAction
