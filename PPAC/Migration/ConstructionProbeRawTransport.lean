/- Pinned ProbePresentations.Raw.transport and its constructor/injectivity laws.
Raw is already an internal finite letter graph plus an old terminal. Transport
composes that graph with the actual alphabet map; no new recursion is needed. -/
import PPAC.Migration.ConstructionProbeAlphabetMapSyntax
import PPAC.Migration.ConstructionProbeReduced

namespace PPAC.Migration.ConstructionProbeRawTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeReduced
open ConstructionProbeMappedPath (NodeMap exists_node_map)
open ConstructionProbeAlphabetMap (DivisionReflection ConeMap ActionMap)
open ConstructionProbeLiftHom (PreservesProducts)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (w D S SN f g q r : M.Carrier .set) : Prop := ∃ n h x H fx,
  (Project.FirstOrderSemantics.reduct M).mem n w ∧ MapsTo n S h ∧
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.Code M q h x ∧
  MapsTo n SN H ∧ PureKuratowski.Code M r H fx ∧ PureKuratowski.PairMember M x fx f ∧ NodeMap h g H

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g q : M.Carrier .set} (hf : MapsTo D N f) (hg : MapsTo S SN g)
    (hq : Raw w D S q) : ∃ r, Value w D S SN f g q r := by
  obtain ⟨h,x,⟨n,hn,hh⟩,hx,hq⟩ := hq
  obtain ⟨H,hH,hmap⟩ := exists_node_map hM hh hg
  obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
  obtain ⟨r,hr⟩ := KuratowskiZF.exists_code hM H fx
  exact ⟨r,n,h,x,H,fx,hn,hh,hx,hq,hH,hr,hfx,hmap⟩

theorem value_raw {w D N S SN f g q r : M.Carrier .set}
    (hf : MapsTo D N f) (h : Value w D S SN f g q r) : Raw w D S q ∧ Raw w N SN r := by
  obtain ⟨n,h,x,H,fx,hn,hh,hx,hq,hH,hr,hfx,_⟩ := h
  exact ⟨⟨h,x,⟨n,hn,hh⟩,hx,hq⟩,⟨H,fx,⟨n,hn,hH⟩,hf.2 x fx hfx,hr⟩⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g q r r' : M.Carrier .set} (hf : MapsTo D N f)
    (hr : Value w D S SN f g q r) (hr' : Value w D S SN f g q r') : r = r' := by
  obtain ⟨n,h,x,H,fx,_,_,_,hq,hH,hr,hfx,hmap⟩ := hr
  obtain ⟨n',h',x',H',fx',_,_,_,hq',hH',hr',hfx',hmap'⟩ := hr'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  have he := function_unique hf.1 hfx hfx'
  subst fx'
  have heH : H = H' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff
    (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM n SN H).mp hH).1.1
    ((ForcingSupportSize.native_mapsTo hM n' SN H').mp hH').1.1
    (fun i y => (hmap i y).trans (hmap' i y).symm)
  subst H'
  exact KuratowskiZF.code_unique hM hr hr'

theorem value_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g q q' r : M.Carrier .set} (hf : Injection D N f) (hg : Injection S SN g)
    (hq : Value w D S SN f g q r) (hq' : Value w D S SN f g q' r) : q = q' := by
  obtain ⟨n,h,x,H,fx,_,hh,_,hq,_,hr,hfx,hmap⟩ := hq
  obtain ⟨n',h',x',H',fx',_,hh',_,hq',_,hr',hfx',hmap'⟩ := hq'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr hr'
  have he := hf.2 x x' fx hfx hfx'
  subst x'
  have heh : h = h' := by
    apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
      ((ForcingSupportSize.native_mapsTo hM n S h).mp hh).1.1
      ((ForcingSupportSize.native_mapsTo hM n' S h').mp hh').1.1
    intro i y
    constructor
    · intro hy
      obtain ⟨gy,hgy,_⟩ := hg.1.1.2 y (hh.2 i y hy)
      obtain ⟨z,hz,hgz⟩ := (hmap' i gy).mp ((hmap i gy).mpr ⟨y,hy,hgy⟩)
      exact (hg.2 z y gy hgz hgy) ▸ hz
    · intro hy
      obtain ⟨gy,hgy,_⟩ := hg.1.1.2 y (hh'.2 i y hy)
      obtain ⟨z,hz,hgz⟩ := (hmap i gy).mp ((hmap' i gy).mpr ⟨y,hy,hgy⟩)
      exact (hg.2 z y gy hgz hgy) ▸ hz
  subst h'
  exact KuratowskiZF.code_unique hM hq hq'

/-- Normalize transport against the already existing representation of q. -/
theorem value_iff_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S SN f g q r n h x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hh : MapsTo n S h)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hq : PureKuratowski.Code M q h x) :
    Value w D S SN f g q r ↔ ∃ H fx, MapsTo n SN H ∧ PureKuratowski.Code M r H fx ∧
      PureKuratowski.PairMember M x fx f ∧ NodeMap h g H := by
  constructor
  · rintro ⟨m,h',x',H,fx,hm,hh',_,hq',hH,hr,hfx,hmap⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    have hZF := ModelTransfer.project_models_iff.mp hM
    have he := SetTheory.Structure.IsSequenceOfLength.length_eq hZF.1
      (native_sequence hM (hw.members_areOrdinals hZF n hn) hh)
      (native_sequence hM (hw.members_areOrdinals hZF m hm) hh')
    subst m
    exact ⟨H,fx,hH,hr,hfx,hmap⟩
  · rintro ⟨H,fx,hH,hr,hfx,hmap⟩
    exact ⟨n,h,x,H,fx,hn,hh,hx,hq,hH,hr,hfx,hmap⟩

theorem transport_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero f g x fx q r : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hf : MapsTo D N f) (hx : Old zero D x q) (hfx : PureKuratowski.PairMember M x fx f)
    (htr : Value w D S SN f g q r) : Old zero N fx r := by
  obtain ⟨n,h,y,H,fy,_,_,_,hq,hH,hr,hfy,hmap⟩ := htr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hx.2 hq
  have he := function_unique hf.1 hfx hfy
  subst fy
  have hEmpty : H = zero := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro p
    constructor
    · intro hp
      obtain ⟨i,z,_,hcode⟩ := hH.1.1 p hp
      obtain ⟨y,⟨v,_,hv⟩,_⟩ := (hmap i z).mp ⟨p,hcode,hp⟩
      exact (hz v hv).elim
    · intro hp
      exact (hz p hp).elim
  subst H
  exact ⟨hf.2 x fx hfx,hr⟩

theorem map_append {h k H K g n s gs : M.Carrier .set}
    {S SN : M.Carrier .set} (hg : MapsTo S SN g)
    (hmap : NodeMap h g H) (kmap : NodeMap k g K) (hgs : PureKuratowski.PairMember M s gs g)
    (happend : ∀ i y, PureKuratowski.PairMember M i y k ↔
      PureKuratowski.PairMember M i y h ∨ (i = n ∧ y = s)) :
    ∀ i y, PureKuratowski.PairMember M i y K ↔
      PureKuratowski.PairMember M i y H ∨ (i = n ∧ y = gs) := by
  intro i y
  constructor
  · intro hy
    obtain ⟨z,hz,hgz⟩ := (kmap i y).mp hy
    rcases (happend i z).mp hz with hz | ⟨rfl,rfl⟩
    · exact Or.inl ((hmap i y).mpr ⟨z,hz,hgz⟩)
    · exact Or.inr ⟨rfl,function_unique hg.1 hgz hgs⟩
  · rintro (hy | ⟨rfl,rfl⟩)
    · obtain ⟨z,hz,hgz⟩ := (hmap i y).mp hy
      exact (kmap i y).mpr ⟨z,(happend i z).mpr (Or.inl hz),hgz⟩
    · exact (kmap i y).mpr ⟨s,(happend i s).mpr (Or.inr ⟨rfl,rfl⟩),hgs⟩

theorem transport_cons (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g s gs t T q Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g)
    (hcons : Cons w D S s t q) (hgs : PureKuratowski.PairMember M s gs g)
    (ht : Value w D S SN f g t T) (hq : Value w D S SN f g q Q) : Cons w N SN gs T Q := by
  obtain ⟨n,m,h,k,x,hn,hm,hSucc,hh,hk,hx,_,htc,hqc,happend⟩ := hcons
  obtain ⟨H,fx,hH,hT,hfx,hmap⟩ := (value_iff_at hM hw hn hh hx htc).mp ht
  obtain ⟨K,fy,hK,hQ,hfy,kmap⟩ := (value_iff_at hM hw hm hk hx hqc).mp hq
  have he := function_unique hf.1 hfx hfy
  subst fy
  exact ⟨n,m,H,K,fx,hn,hm,hSucc,hH,hK,hf.2 x fx hfx,hg.2 s gs hgs,hT,hQ,
    map_append hg hmap kmap hgs happend⟩

/-- Original head/cone tests at every internal prefix, including nonstandard lengths. -/
theorem prefixHead_transport {D N S SN mul mulN A AN b fb n h H x fx f g : M.Carrier .set}
    (hg : MapsTo S SN g) (hh : MapsTo n S h) (hmap : NodeMap h g H)
    (hDiv : DivisionReflection D N mul mulN f) (hCone : ConeMap S SN A AN f g)
    (hb : PureKuratowski.PairMember M b fb f) (hx : PureKuratowski.PairMember M x fx f)
    (k : M.Carrier .set) : PrefixHead N SN mulN AN fb k H fx ↔ PrefixHead D S mul A b k h x := by
  constructor
  · rintro (⟨hk,hd⟩ | ⟨j,gs,hSucc,hgs,hc⟩)
    · exact Or.inl ⟨hk,(hDiv b x fb fx hb hx).mp hd⟩
    · obtain ⟨s,hs,hgs⟩ := (hmap j gs).mp hgs
      exact Or.inr ⟨j,s,hSucc,hs,(hCone b s fb gs hb hgs).mp hc⟩
  · rintro (⟨hk,hd⟩ | ⟨j,s,hSucc,hs,hc⟩)
    · exact Or.inl ⟨hk,(hDiv b x fb fx hb hx).mpr hd⟩
    · obtain ⟨gs,hgs,_⟩ := hg.1.2 s (hh.2 j s hs)
      exact Or.inr ⟨j,gs,hSucc,(hmap j gs).mpr ⟨s,hs,hgs⟩,(hCone b s fb gs hb hgs).mpr hc⟩

theorem reduced_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN mul mulN A AN b fb f g q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g)
    (hDiv : DivisionReflection D N mul mulN f) (hCone : ConeMap S SN A AN f g)
    (hb : PureKuratowski.PairMember M b fb f) (htr : Value w D S SN f g q r) :
    Reduced w N SN mulN AN fb r ↔ Reduced w D S mul A b q := by
  obtain ⟨n,h,x,H,fx,hn,hh,hx,hq,hH,hr,hfx,hmap⟩ := htr
  rw [reduced_iff_at hM hw hn hH (hf.2 x fx hfx) hr,reduced_iff_at hM hw hn hh hx hq]
  exact ⟨fun hgood k hk hd => hgood k hk ((prefixHead_transport hg hh hmap hDiv hCone hb hfx k).mpr hd),
    fun hgood k hk hd => hgood k hk ((prefixHead_transport hg hh hmap hDiv hCone hb hfx k).mp hd)⟩

theorem headDiv_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g)
    (hDiv : DivisionReflection D N mul mulN f) (hCone : ConeMap S SN A AN f g)
    (hb : PureKuratowski.PairMember M b fb f) (htr : Value w D S SN f g q r) :
    HeadDiv w N SN zero mulN AN fb r ↔ HeadDiv w D S zero mul A b q := by
  obtain ⟨n,h,x,H,fx,hn,hh,hx,hq,hH,hr,hfx,hmap⟩ := htr
  exact (prefixHead_iff_headDiv hM hw hz hzw hn hH (hf.2 x fx hfx) hr).symm.trans
    ((prefixHead_transport hg hh hmap hDiv hCone hb hfx n).trans
      (prefixHead_iff_headDiv hM hw hz hzw hn hh hx hq))

theorem transport_oldAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g q r q' r' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hPres : PreservesProducts mul mulN f)
    (hAct : ActionMap A AN f g) (hb : PureKuratowski.PairMember M b fb f)
    (hq : Value w D S SN f g q r) (hq' : Value w D S SN f g q' r')
    (hact : OldAct w D S zero mul A b q q') : OldAct w N SN zero mulN AN fb r r' := by
  refine ⟨hf.2 b fb hb,?_⟩
  rcases hact.2 with ⟨x,y,hx,hxy,hy⟩ | ⟨s,t,v,hst,hsv,hvt⟩
  · obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx.1
    obtain ⟨fy,hfy,_⟩ := hf.1.2 y hy.1
    exact Or.inl ⟨fx,fy,transport_old hM hz hf hx hfx hq,
      hPres b x y fb fx fy hxy hb hfx hfy,transport_old hM hz hf hy hfy hq'⟩
  · obtain ⟨gs,hgs,_⟩ := hg.1.2 s (cons_letter hst)
    obtain ⟨gv,hgv,_⟩ := hg.1.2 v (cons_letter hvt)
    obtain ⟨T,hT⟩ := value_total hM hf hg (cons_raw hst).1
    exact Or.inr ⟨gs,T,gv,transport_cons hM hw hf hg hst hgs hT hq,
      hAct b s v fb gs gv hsv hb hgs hgv,transport_cons hM hw hf hg hvt hgv hT hq'⟩


def Graph (w D S SN f g H : M.Carrier .set) : Prop := ∀ q r,
  PureKuratowski.PairMember M q r H ↔ Value w D S SN f g q r

def ConstructorLaws (w D N S SN zero f g H : M.Carrier .set) : Prop :=
  (∀ x fx q r, PureKuratowski.PairMember M x fx f → Old zero D x q →
    PureKuratowski.PairMember M q r H → Old zero N fx r) ∧
  (∀ s gs t T q Q, PureKuratowski.PairMember M s gs g → Cons w D S s t q →
    PureKuratowski.PairMember M t T H → PureKuratowski.PairMember M q Q H → Cons w N SN gs T Q)

theorem constructor_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero f g H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hG : Graph w D S SN f g H) :
    ConstructorLaws w D N S SN zero f g H :=
  ⟨fun _ _ _ _ hfx hx hqr => transport_old hM hz hf hx hfx ((hG _ _).mp hqr),
    fun _ _ _ _ _ _ hgs hcons ht hq => transport_cons hM hw hf hg hcons hgs ((hG _ _).mp ht) ((hG _ _).mp hq)⟩

def SimulationLaws (w D N S SN zero mul mulN A AN f H : M.Carrier .set) : Prop :=
  (∀ b fb q r, PureKuratowski.PairMember M b fb f → PureKuratowski.PairMember M q r H →
    (HeadDiv w N SN zero mulN AN fb r ↔ HeadDiv w D S zero mul A b q) ∧
    (Reduced w N SN mulN AN fb r ↔ Reduced w D S mul A b q)) ∧
  (∀ b fb q r q' r', PureKuratowski.PairMember M b fb f → PureKuratowski.PairMember M q r H →
    PureKuratowski.PairMember M q' r' H → OldAct w D S zero mul A b q q' →
      OldAct w N SN zero mulN AN fb r r')

theorem simulation_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN f g H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g)
    (hDiv : DivisionReflection D N mul mulN f) (hCone : ConeMap S SN A AN f g)
    (hPres : PreservesProducts mul mulN f) (hAct : ActionMap A AN f g)
    (hG : Graph w D S SN f g H) : SimulationLaws w D N S SN zero mul mulN A AN f H :=
  ⟨fun _ _ _ _ hb hqr =>
    ⟨headDiv_transport hM hw hz hzw hf hg hDiv hCone hb ((hG _ _).mp hqr),
      reduced_transport hM hw hf hg hDiv hCone hb ((hG _ _).mp hqr)⟩,
    fun _ _ _ _ _ _ hb hqr hqr' hact =>
      transport_oldAct hM hw hz hf hg hPres hAct hb ((hG _ _).mp hqr) ((hG _ _).mp hqr') hact⟩

end PPAC.Migration.ConstructionProbeRawTransport
