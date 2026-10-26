/- Pinned ProbePresentations.Path.map/map_factor/map_terminal.
Construct the image node graph using native composition, then reuse the existing
path-table constructors. No mapped path or factor equations are assumed. -/
import PPAC.Migration.ConstructionProbeLiftHomSyntax

namespace PPAC.Migration.ConstructionProbeMappedPath
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePath
open ConstructionProbeLiftHom (PreservesProducts)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def NodeMap (node f mapped : M.Carrier .set) : Prop := ∀ i y,
  PureKuratowski.PairMember M i y mapped ↔ ∃ x,
    PureKuratowski.PairMember M i x node ∧ PureKuratowski.PairMember M x y f

def FactorMap (F G f : M.Carrier .set) : Prop := ∀ i j x y,
  Product F i j x → PureKuratowski.PairMember M x y f → Product G i j y

def TerminalMap (T U f : M.Carrier .set) : Prop := ∀ i x y,
  PureKuratowski.PairMember M i x T → PureKuratowski.PairMember M x y f →
    PureKuratowski.PairMember M i y U

theorem exists_node_map (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N node f : M.Carrier .set} (hn : MapsTo w D node) (hf : MapsTo D N f) :
    ∃ mapped, MapsTo w N mapped ∧ NodeMap node f mapped := by
  obtain ⟨mapped,hm,he⟩ := ZF.exists_compositionFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) ((ForcingSupportSize.native_mapsTo hM w D node).mp hn)
    ((ForcingSupportSize.native_mapsTo hM D N f).mp hf)
  refine ⟨mapped,(ForcingSupportSize.native_mapsTo hM w N mapped).mpr hm,fun i y => ?_⟩
  exact (he i y).trans ⟨fun ⟨_,x,hx,hy⟩ => ⟨x,hx,hy⟩,
    fun ⟨x,hx,hy⟩ => ⟨function_input hn.1 hx,x,hx,hy⟩⟩

theorem mapped_factor {w D N mul mulN node mapped f i j x y : M.Carrier .set}
    (hn : MapsTo w D node) (hf : MapsTo D N f) (hmap : NodeMap node f mapped)
    (hPres : PreservesProducts mul mulN f)
    (hx : Factor D mul node i j x) (hxy : PureKuratowski.PairMember M x y f) :
    Factor N mulN mapped i j y := by
  obtain ⟨ni,nj,hi,hj,_,hmul⟩ := hx
  obtain ⟨fi,hfi,_⟩ := hf.1.2 ni (hn.2 i ni hi)
  obtain ⟨fj,hfj,_⟩ := hf.1.2 nj (hn.2 j nj hj)
  exact ⟨fi,fj,(hmap i fi).mpr ⟨ni,hi,hfi⟩,(hmap j fj).mpr ⟨nj,hj,hfj⟩,
    hf.2 x y hxy,hPres ni x nj fi y fj hmul hfi hxy hfj⟩

theorem mapped_terminal {w D N mul mulN node mapped f a fa i x y : M.Carrier .set}
    (hn : MapsTo w D node) (hf : MapsTo D N f) (hmap : NodeMap node f mapped)
    (hPres : PreservesProducts mul mulN f) (ha : PureKuratowski.PairMember M a fa f)
    (hx : Terminal D mul node a i x) (hxy : PureKuratowski.PairMember M x y f) :
    Terminal N mulN mapped fa i y := by
  obtain ⟨ni,hi,_,hmul⟩ := hx
  obtain ⟨fi,hfi,_⟩ := hf.1.2 ni (hn.2 i ni hi)
  exact ⟨fi,(hmap i fi).mpr ⟨ni,hi,hfi⟩,hf.2 x y hxy,
    hPres ni x a fi y fa hmul hfi hxy ha⟩

theorem mapped_path {w D N mul mulN e eN zero a fa node mapped f : M.Carrier .set}
    (hp : Path w D mul e zero a node) (hf : MapsTo D N f)
    (hmapped : MapsTo w N mapped) (hmap : NodeMap node f mapped)
    (hPres : PreservesProducts mul mulN f) (hOne : PureKuratowski.PairMember M e eN f)
    (ha : PureKuratowski.PairMember M a fa f) : Path w N mulN eN zero fa mapped := by
  refine ⟨hmapped,hf.2 a fa ha,(hmap zero eN).mpr ⟨e,hp.2.2.1,hOne⟩,?_,?_⟩
  · intro i j hi hj hij
    obtain ⟨x,hx⟩ := hp.2.2.2.1 i j hi hj hij
    obtain ⟨ni,nj,hni,hnj,hxD,hprod⟩ := hx
    obtain ⟨y,hxy,_⟩ := hf.1.2 x hxD
    exact ⟨y,mapped_factor hp.1 hf hmap hPres ⟨ni,nj,hni,hnj,hxD,hprod⟩ hxy⟩
  · intro i hi
    obtain ⟨x,ni,hni,hxD,hprod⟩ := hp.2.2.2.2 i hi
    obtain ⟨y,hxy,_⟩ := hf.1.2 x hxD
    exact ⟨y,mapped_terminal hp.1 hf hmap hPres ha ⟨ni,hni,hxD,hprod⟩ hxy⟩

theorem factor_map {w D N mul mulN e zero a node mapped f F G : M.Carrier .set}
    (hp : Path w D mul e zero a node) (hf : MapsTo D N f) (hmap : NodeMap node f mapped)
    (hPres : PreservesProducts mul mulN f)
    (hF : FactorTable w D mul node F) (hG : FactorTable w N mulN mapped G) : FactorMap F G f := by
  intro i j x y hx hxy
  obtain ⟨hi,hj,hij,hx⟩ := (hF i j x).mp hx
  exact (hG i j y).mpr ⟨hi,hj,hij,mapped_factor hp.1 hf hmap hPres hx hxy⟩

theorem terminal_map {w D N mul mulN e zero a fa node mapped f T U : M.Carrier .set}
    (hp : Path w D mul e zero a node) (hf : MapsTo D N f) (hmap : NodeMap node f mapped)
    (hPres : PreservesProducts mul mulN f) (ha : PureKuratowski.PairMember M a fa f)
    (hT : TerminalTable w D mul node a T) (hU : TerminalTable w N mulN mapped fa U) : TerminalMap T U f := by
  intro i x y hx hxy
  obtain ⟨hi,hx⟩ := (hT i x).mp hx
  exact (hU i y).mpr ⟨hi,mapped_terminal hp.1 hf hmap hPres ha hx hxy⟩

theorem exists_mapped_path (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F T N mulN eN f fa : M.Carrier .set}
    (hp : Path w D mul e zero a node) (hF : FactorTable w D mul node F)
    (hT : TerminalTable w D mul node a T) (hmN : LeftCancelMonoid N mulN eN)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f) (ha : PureKuratowski.PairMember M a fa f) :
    ∃ mapped pairs G U, NodeMap node f mapped ∧ Path w N mulN eN zero fa mapped ∧
      OrderedPairs w pairs ∧ MapsTo pairs N G ∧ FactorTable w N mulN mapped G ∧
      MapsTo w N U ∧ TerminalTable w N mulN mapped fa U ∧ FactorMap F G f ∧ TerminalMap T U f := by
  obtain ⟨mapped,hmapped,hmap⟩ := exists_node_map hM hp.1 hf
  have hpath := mapped_path hp hf hmapped hmap hPres hOne ha
  obtain ⟨pairs,hpairs⟩ := exists_ordered_pairs hM w
  obtain ⟨G,hGmap,hG⟩ := exists_factor_table hM hmN hpath hpairs
  obtain ⟨U,hUmap,hU⟩ := exists_terminal_table hM hmN hpath
  exact ⟨mapped,pairs,G,U,hmap,hpath,hpairs,hGmap,hG,hUmap,hU,
    factor_map hp hf hmap hPres hF hG,terminal_map hp hf hmap hPres ha hT hU⟩

end PPAC.Migration.ConstructionProbeMappedPath
