/- Pinned MonoidBase.Object/Hom.comp and MonoidRounds.Round.step.
Only pure abbreviations of accepted source fields, for the actual step.
Reuse native composition/Conservative/Cap/profile interfaces throughout. -/
import PPAC.Migration.ConstructionProbeParent
import PPAC.Migration.ConstructionMergerParent
import PPAC.Migration.ConstructionRequestMapsSyntax
import PPAC.Migration.ConstructionDirectedHeightCost

namespace PPAC.Migration.ConstructionRoundFields
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeConservative (Conservative)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionPersistentProfiles (ProbeProfile HasOldGates)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ObjectFields (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C : M.Carrier .set) : Prop :=
  LeftCancelMonoid D mul e ∧ Conical D mul e ∧ ConstructionProbeSharedIntersections.ConditionalJoins D mul ∧
    (Project.FirstOrderSemantics.reduct M).mem mark D ∧ mark ≠ e ∧
    MapsTo D R H ∧ ConstructionCutWeights.RangeBound top H ∧ MapsTo D R C ∧ ConstructionProbeGateCap.Bounds top C ∧
    ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul H C ∧
    ConstructionDirectedHeightCost.ExactMargins hM w Q D mul H C ∧
    ∃ B, ConstructionProbeLetters.Representatives D D B ∧ MapsTo B D mul

def MapFields (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q D N mul mulN e eN mark markN H C HN CN f : M.Carrier .set) : Prop :=
  Conservative D N mul mulN f ∧ PreservesProducts mul mulN f ∧
    PureKuratowski.PairMember M e eN f ∧ PureKuratowski.PairMember M mark markN f ∧
    (∀ x fx r, PureKuratowski.PairMember M x fx f →
      (PureKuratowski.PairMember M fx r HN ↔ PureKuratowski.PairMember M x r H)) ∧
    (∀ x fx r, PureKuratowski.PairMember M x fx f →
      (PureKuratowski.PairMember M fx r CN ↔ PureKuratowski.PairMember M x r C)) ∧
    ConstructionDirectedHeightCost.OldSuprema hM w Q D N mul mulN C CN f

def Profiles (w D N mul mulN f : M.Carrier .set) : Prop :=
  ∀ a b d p node, ProbeProfile w D mul a b d p node →
    ∃ mapped fa fb fd fp, NodeMap node f mapped ∧ PureKuratowski.PairMember M a fa f ∧
      PureKuratowski.PairMember M b fb f ∧ PureKuratowski.PairMember M d fd f ∧
      PureKuratowski.PairMember M p fp f ∧ ProbeProfile w N mulN fa fb fd fp mapped

def SizeBound (hM : FirstOrder.Theory.Models M nativeZF) (w D N : M.Carrier .set) : Prop :=
  ∀ mu, (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
    ForcingSupportSize.Small D mu → ForcingSupportSize.Small N mu

def Successor (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero D mul e mark H C N mulN eN markN HN CN O : M.Carrier .set) : Prop :=
  ObjectFields hM w Q R top N mulN eN markN HN CN ∧
    MapFields hM w Q D N mul mulN e eN mark markN H C HN CN O ∧
    ConstructionProbeOldEmbedding.OldGraph zero D O ∧ HasOldGates D N mul mulN O ∧
    Profiles w D N mul mulN O ∧ SizeBound hM w D N

theorem node_comp {node f g h mid last : M.Carrier .set}
    (hC : NodeMap f g h) (h1 : NodeMap node f mid) (h2 : NodeMap mid g last) : NodeMap node h last := by
  intro i z
  constructor
  · intro hz
    obtain ⟨y,hiy,hyz⟩ := (h2 i z).mp hz
    obtain ⟨x,hix,hxy⟩ := (h1 i y).mp hiy
    exact ⟨x,hix,(hC x z).mpr ⟨y,hxy,hyz⟩⟩
  · rintro ⟨x,hix,hxz⟩
    obtain ⟨y,hxy,hyz⟩ := (hC x z).mp hxz
    exact (h2 i z).mpr ⟨y,(h1 i y).mpr ⟨x,hix,hxy⟩,hyz⟩

theorem profiles_comp {w D N R mul mulN mulR f g h : M.Carrier .set}
    (hC : NodeMap f g h) (hf : Profiles w D N mul mulN f) (hg : Profiles w N R mulN mulR g) :
    Profiles w D R mul mulR h := by
  intro a b d p node hp
  obtain ⟨mid,fa,fb,fd,fp,hm,ha,hb,hd,hp',hProf⟩ := hf a b d p node hp
  obtain ⟨last,ga,gb,gd,gp,hl,hga,hgb,hgd,hgp,hFinal⟩ := hg fa fb fd fp mid hProf
  exact ⟨last,ga,gb,gd,gp,node_comp hC hm hl,(hC a ga).mpr ⟨fa,ha,hga⟩,
    (hC b gb).mpr ⟨fb,hb,hgb⟩,(hC d gd).mpr ⟨fd,hd,hgd⟩,(hC p gp).mpr ⟨fp,hp',hgp⟩,hFinal⟩

theorem map_comp (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D N R mul mulN mulR e eN eR mark markN markR H C HN CN HR CR f g h : M.Carrier .set}
    (hmN : LeftCancelMonoid N mulN eN) (hmR : LeftCancelMonoid R mulR eR)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hg : MapFields hM w Q N R mulN mulR eN eR markN markR HN CN HR CR g)
    (hh : MapsTo D R h) (hComp : NodeMap f g h) :
    MapFields hM w Q D R mul mulR e eR mark markR H C HR CR h := by
  obtain ⟨hfCons,hfProd,hfOne,hfMark,hfH,hfC,hfSup⟩ := hf
  obtain ⟨hgCons,hgProd,hgOne,hgMark,hgH,hgC,hgSup⟩ := hg
  have hCon : Conservative D R mul mulR h := by
    refine ⟨⟨hh,?_⟩,?_,?_,?_⟩
    · intro x y z hx hy
      obtain ⟨a,hxa,haz⟩ := (hComp x z).mp hx
      obtain ⟨b,hyb,hbz⟩ := (hComp y z).mp hy
      have hab := hgCons.1.2 a b z haz hbz
      exact hfCons.1.2 x y a hxa (hab.symm ▸ hyb)
    · intro x y z fx fy hx hy hz hprod
      obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
      obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
      obtain ⟨t,ht,hat⟩ := ConstructionProbeAlphabetMap.factor_eq hmN hmR hgCons.1 hgProd hgCons.2.1 haf hbf hz hprod
      obtain ⟨u,hu⟩ := hfCons.2.1 x y t a b hxa hyb (ForcingConditionGraphs.function_input hgCons.1.1.1 ht) hat
      exact ⟨u,(hComp u z).mpr ⟨t,hu,ht⟩⟩
    · intro x y j fx fy fj hx hy hj hJoin
      obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
      obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
      obtain ⟨c,hjc,hcf⟩ := (hComp j fj).mp hj
      exact hgCons.2.2.1 a b c fx fy fj haf hbf hcf (hfCons.2.2.1 x y j a b c hxa hyb hjc hJoin)
    · intro x y fx fy hx hy hCommon
      obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
      obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
      exact hfCons.2.2.2 x y a b hxa hyb (hgCons.2.2.2 a b fx fy haf hbf hCommon)
  refine ⟨hCon,?_,(hComp e eR).mpr ⟨eN,hfOne,hgOne⟩,
    (hComp mark markR).mpr ⟨markN,hfMark,hgMark⟩,?_,?_,?_⟩
  · intro x y z fx fy fz hxyz hx hy hz
    obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
    obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
    obtain ⟨c,hzc,hcf⟩ := (hComp z fz).mp hz
    exact hgProd a b c fx fy fz (hfProd x y z a b c hxyz hxa hyb hzc) haf hbf hcf
  · intro x z r hx
    obtain ⟨y,hxy,hyz⟩ := (hComp x z).mp hx
    exact (hgH y z r hyz).trans (hfH x y r hxy)
  · intro x z r hx
    obtain ⟨y,hxy,hyz⟩ := (hComp x z).mp hx
    exact (hgC y z r hyz).trans (hfC x y r hxy)
  · intro x y fx fy hx hy
    obtain ⟨a,hxa,haf⟩ := (hComp x fx).mp hx
    obtain ⟨b,hyb,hbf⟩ := (hComp y fy).mp hy
    obtain ⟨f0,f1,cap,hF0,_,hCut,hCap0,hCap1,_⟩ := hfSup x y a b hxa hyb
    obtain ⟨g1,g2,cap',_,hF2,_,hCap1',hCap2,_⟩ := hgSup a b fx fy haf hbf
    have heq := ConstructionProbeCostSupremum.cap_unique hM hCap1 hCap1'
    subst cap'
    exact ⟨f0,g2,cap,hF0,hF2,hCut,hCap0,hCap2,fun c0 c1 hc0 hc1 =>
      (ConstructionProbeCostSupremum.cap_unique hM hc0 hCap0).trans (ConstructionProbeCostSupremum.cap_unique hM hCap2 hc1)⟩

theorem exists_fromBase (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D N R mul mulN mulR e eN eR mark markN markR H C HN CN HR CR f g : M.Carrier .set}
    (hmN : LeftCancelMonoid N mulN eN) (hmR : LeftCancelMonoid R mulR eR)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hg : MapFields hM w Q N R mulN mulR eN eR markN markR HN CN HR CR g) :
    ∃ h, MapsTo D R h ∧ NodeMap f g h ∧ MapFields hM w Q D R mul mulR e eR mark markR H C HR CR h := by
  obtain ⟨h,hh,hComp⟩ := ConstructionProbeMappedPath.exists_node_map hM hf.1.1.1 hg.1.1.1
  exact ⟨h,hh,hComp,map_comp hM hmN hmR hf hg hh hComp⟩

end PPAC.Migration.ConstructionRoundFields
