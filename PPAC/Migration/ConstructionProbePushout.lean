/- Pinned Construction/MergerPushouts.Path.simulation_pushout: actual indexed
presentation lift into any internal monoid. Reuse existing graph composition,
presented lift, extensionality, and the actual conservative simulation. -/
import PPAC.Migration.ConstructionProbePresentedLiftSyntax
import PPAC.Migration.ConstructionProbeSimulation
import PPAC.Migration.ConstructionProbeMappedPathSyntax

namespace PPAC.Migration.ConstructionProbePushout
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeOldEmbedding (OldGraph old_word)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet ExitGraph)
open ConstructionProbeTarget (TargetGraph)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeMappedPath (NodeMap FactorMap TerminalMap exists_node_map)
open ConstructionProbePath (Path FactorTable)
open ConstructionProbeLetters (Representatives Letters Projection EqualityLaw)
open ConstructionProbeAction (ActionTable)
open ConstructionProbeGenerator (GeneratorGraph)
open ConstructionProbeIndexedGenerators (ProbeGraph)
open ConstructionProbePresentedLift (ProbeRelations IndexedExit PresentedLaws)
open ConstructionProbePresentationTransitions (Adjacent)
open ConstructionProbeSimulation (EndpointLaws)
open ConstructionProbeConservative (Conservative)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Unit Associative)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Only previously proved concrete graph contracts, no universal-property field. -/
structure Presentation (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O : M.Carrier .set) : Prop where
  monoid : LeftCancelMonoid D mul e
  alphabet : Alphabet D mul e S I act E
  word : WordCarrier w D S mul act b W
  b_mem : (Project.FirstOrderSemantics.reduct M).mem b D
  old_unit : Old zero D e unit
  multiplication : MultiplicationGraph hM w D S zero mul act b W E G
  generators_map : MapsTo S W K
  generators : GeneratorGraph w D S unit K
  representatives : Representatives w D C
  letters : Letters w D mul factor C S
  projection_map : MapsTo C S projection
  projection_law : Projection w D mul factor C projection
  equality : EqualityLaw w D mul factor projection
  action : ActionTable D mul projection act
  path : Path w D mul e zero a node
  factors : FactorTable w D mul node factor
  probes_map : MapsTo w W P
  probes : ProbeGraph w projection e K P
  terminals_map : MapsTo w D terminal
  target_law : TargetGraph D mul projection terminal target
  exit_law : ExitGraph mul target d E
  d_mem : (Project.FirstOrderSemantics.reduct M).mem d D
  old_graph : OldGraph zero D O
  old_map : MapsTo D W O

def Hom (D N mul mulN e eN F : M.Carrier .set) : Prop :=
  MapsTo D N F ∧ PureKuratowski.PairMember M e eN F ∧ PreservesProducts mul mulN F

/-- Equality of the two composites, stated using their actual graph values. -/
def SquareComm (O f s t : M.Carrier .set) : Prop := ∀ x q fx y,
  PureKuratowski.PairMember M x q O → PureKuratowski.PairMember M x fx f →
    (PureKuratowski.PairMember M q y s ↔ PureKuratowski.PairMember M fx y t)

/-- Source IsPushout: universal target is an arbitrary internal monoid. -/
def IsPushout (N W WN mulN G GN eN unit unitN O f H ON : M.Carrier .set) : Prop :=
  SquareComm O f H ON ∧ ∀ Q J mulQ eQ s t,
    Representatives Q Q J → MapsTo J Q mulQ → Unit Q mulQ eQ → Associative Q mulQ →
    Hom W Q G mulQ unit eQ s → Hom N Q mulN mulQ eN eQ t → SquareComm O f s t →
    ∃ L, Hom WN Q GN mulQ unitN eQ L ∧ NodeMap H L s ∧ NodeMap ON L t ∧
      ∀ R, Hom WN Q GN mulQ unitN eQ R → NodeMap H R s → NodeMap ON R t → R = L

theorem composition_value {D N f g comp x y z : M.Carrier .set}
    (hf : MapsTo D N f) (hc : NodeMap f g comp) (hxy : PureKuratowski.PairMember M x y f) :
    PureKuratowski.PairMember M x z comp ↔ PureKuratowski.PairMember M y z g := by
  constructor
  · intro h
    obtain ⟨y',hy',hg⟩ := (hc x z).mp h
    exact (function_unique hf.1 hy' hxy) ▸ hg
  · intro h
    exact (hc x z).mpr ⟨y,hxy,h⟩

theorem composition_preserves {mulD mulN mulQ f g comp : M.Carrier .set}
    (hc : NodeMap f g comp) (hf : PreservesProducts mulD mulN f)
    (hg : PreservesProducts mulN mulQ g) : PreservesProducts mulD mulQ comp := by
  intro x y z fx fy fz hp hx hy hz
  obtain ⟨mx,hmx,hfx⟩ := (hc x fx).mp hx
  obtain ⟨my,hmy,hfy⟩ := (hc y fy).mp hy
  obtain ⟨mz,hmz,hfz⟩ := (hc z fz).mp hz
  exact hg mx my mz fx fy fz (hf x y z mx my mz hp hmx hmy hmz) hfx hfy hfz

section Actual
variable {hM : FirstOrder.Theory.Models M nativeZF}
variable {w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O : M.Carrier .set}
variable (hA : Presentation hM w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O)
include hA

theorem presentation_relations
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) :
    ProbeRelations zero D mul b d terminal factor P G :=
  ConstructionProbePresentedLift.probe_relations hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem
    hA.old_unit hA.multiplication hA.generators_map hA.generators hA.representatives hA.projection_map
    hA.equality hA.action hA.path hA.factors hA.probes hA.terminals_map hA.target_law hA.exit_law

theorem presentation_ext
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    {Q J mulQ R L : M.Carrier .set} (hMul : MapsTo J Q mulQ)
    (hR : MapsTo W Q R) (hL : MapsTo W Q L)
    (hRP : PreservesProducts G mulQ R) (hLP : PreservesProducts G mulQ L)
    (hOld : ∀ x q, Old zero D x q → ConstructionProbeHomExt.AgreeAt q R L)
    (hNew : ∀ i q, PureKuratowski.PairMember M i q P → ConstructionProbeHomExt.AgreeAt q R L) : R = L :=
  ConstructionProbeIndexedGenerators.presentedHom_ext hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem
    hA.old_unit hA.multiplication hA.generators_map hA.generators hA.representatives hA.letters
    hA.projection_map hA.projection_law hA.action hA.probes_map hA.probes hMul hR hL hRP hLP hOld hNew

theorem presentation_lift
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    {Q J mulQ eQ t p : M.Carrier .set}
    (hJ : Representatives Q Q J) (hMul : MapsTo J Q mulQ) (ht : Hom D Q mul mulQ e eQ t)
    (hp : MapsTo w Q p) (hUnit : Unit Q mulQ eQ) (hAssoc : Associative Q mulQ)
    (hAdj : Adjacent w factor t p mulQ) (hExit : IndexedExit terminal mul d b t p mulQ) :
    ∃ L, Hom W Q G mulQ unit eQ L ∧ PresentedLaws zero D G mulQ unit eQ t p P L := by
  obtain ⟨L,hL,hLaw,_⟩ := ConstructionProbePresentedLift.existsUnique_presentedHom hM hw hz hzw
    hA.monoid hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication hA.generators_map hA.generators
    hA.representatives hA.letters hA.projection_map hA.projection_law hA.equality hA.action hA.path hA.factors
    hA.probes_map hA.probes hJ hMul ht.1 hp ht.2.1 hUnit hAssoc ht.2.2 hAdj hA.terminals_map hA.target_law hA.exit_law hA.d_mem hExit
  exact ⟨L,⟨hL,hLaw.1.1,hLaw.1.2.1⟩,hLaw⟩

variable {N mulN eN aN bN dN nodeN factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON f H : M.Carrier .set}
variable (hB : Presentation hM w zero N mulN eN aN bN dN nodeN factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON)
include hB

theorem factor_preimage (hf : MapsTo D N f) (hFactor : FactorMap factor factorN f)
    {i j rN : M.Carrier .set} (hrN : Product factorN i j rN) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r D ∧ Product factor i j r ∧ PureKuratowski.PairMember M r rN f := by
  obtain ⟨hi,hj,hij,hfactorN⟩ := (hB.factors i j rN).mp hrN
  obtain ⟨r,hr⟩ := hA.path.2.2.2.1 i j hi hj hij
  have hrD : (Project.FirstOrderSemantics.reduct M).mem r D := by
    obtain ⟨_,_,_,_,hrD,_⟩ := hr
    exact hrD
  have hfr := (hA.factors i j r).mpr ⟨hi,hj,hij,hr⟩
  obtain ⟨fr,hfrmap,_⟩ := hf.1.2 r hrD
  have he := ConstructionProbePath.factor_unique hB.monoid hB.path.1
    ((hB.factors i j fr).mp (hFactor i j r fr hfr hfrmap)).2.2.2 hfactorN
  exact ⟨r,hrD,hfr,he ▸ hfrmap⟩

theorem terminal_preimage (hf : MapsTo D N f) (hTerminal : TerminalMap terminal terminalN f)
    {i tN : M.Carrier .set} (htN : PureKuratowski.PairMember M i tN terminalN) :
    ∃ t, (Project.FirstOrderSemantics.reduct M).mem t D ∧ PureKuratowski.PairMember M i t terminal ∧ PureKuratowski.PairMember M t tN f := by
  obtain ⟨t,ht,_⟩ := hA.terminals_map.1.2 i (function_input hB.terminals_map.1 htN)
  have htD := hA.terminals_map.2 i t ht
  obtain ⟨ft,hft,_⟩ := hf.1.2 t htD
  have he := function_unique hB.terminals_map.1 (hTerminal i t ft ht hft) htN
  exact ⟨t,htD,ht,he ▸ hft⟩

theorem mapped_relations
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f)
    (hb : PureKuratowski.PairMember M b bN f) (hd : PureKuratowski.PairMember M d dN f)
    (hFactor : FactorMap factor factorN f) (hTerminal : TerminalMap terminal terminalN f)
    {Q mulQ eQ s t p : M.Carrier .set} (hs : Hom W Q G mulQ unit eQ s)
    (hc : SquareComm O f s t) (hp : NodeMap P s p) :
    Adjacent w factorN t p mulQ ∧ IndexedExit terminalN mulN dN bN t p mulQ := by
  have rel := presentation_relations hA hw hz hzw
  constructor
  · intro i j _ _ _ rN tr pi pj hrN htr hpi hpj
    obtain ⟨r,hrD,hr,hfr⟩ := factor_preimage hA hB hf hFactor hrN
    obtain ⟨qi,hqi,hsi⟩ := (hp i pi).mp hpi
    obtain ⟨qj,hqj,hsj⟩ := (hp j pj).mp hpj
    obtain ⟨orw,hor⟩ := exists_old hM (zero := zero) hrD
    have hsor := (hc r orw rN tr ((hA.old_graph r orw).mpr hor) hfr).mpr htr
    exact hs.2.2 orw qj qi tr pj pi (rel.2 i j r qi qj orw hr hqi hqj hor) hsor hsj hsi
  · intro i tN vN pi tb tv htN hprod hpi htb htv
    obtain ⟨r,hrD,hr,hfr⟩ := terminal_preimage hA hB hf hTerminal htN
    obtain ⟨v,hv,hprodv⟩ := (hA.monoid.2.1 r hrD).1 d hA.d_mem
    obtain ⟨fv,hfv,_⟩ := hf.1.2 v hv
    have he := (hB.monoid.2.1 tN (hB.terminals_map.2 i tN htN)).2.1 dN fv vN hB.d_mem
      (hPres r d v tN dN fv hprodv hfr hd hfv) hprod
    have hfvN := he ▸ hfv
    obtain ⟨qi,hqi,hsi⟩ := (hp i pi).mp hpi
    obtain ⟨ob,hob⟩ := exists_old hM (zero := zero) hA.b_mem
    obtain ⟨ov,hov⟩ := exists_old hM (zero := zero) hv
    have hsb := (hc b ob bN tb ((hA.old_graph b ob).mpr hob) hb).mpr htb
    have hsv := (hc v ov vN tv ((hA.old_graph v ov).mpr hov) hfvN).mpr htv
    exact hs.2.2 qi ob ov pi tb tv (rel.1 i qi r v ob ov hqi hr hprodv hob hov) hsi hsb hsv

omit hA in
theorem simulation_commutes (hf : MapsTo D N f) (hH : MapsTo W WN H)
    (hEnd : EndpointLaws f H O ON P PN) : SquareComm O f H ON := by
  intro x q fx y hq hfx
  constructor
  · intro hy
    obtain ⟨Q,hQ,_⟩ := hB.old_map.1.2 fx (hf.2 x fx hfx)
    have he := function_unique hH.1 (hEnd.1 x fx q Q hfx hq hQ) hy
    exact he ▸ hQ
  · intro hy
    exact hEnd.1 x fx q y hfx hq hy

theorem simulation_pushout
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f)
    (hb : PureKuratowski.PairMember M b bN f) (hd : PureKuratowski.PairMember M d dN f)
    (hFactor : FactorMap factor factorN f) (hTerminal : TerminalMap terminal terminalN f)
    (hH : Hom W WN G GN unit unitN H) (hEnd : EndpointLaws f H O ON P PN) :
    IsPushout N W WN mulN G GN eN unit unitN O f H ON := by
  refine ⟨simulation_commutes hB hf hH.1 hEnd,?_⟩
  intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
  obtain ⟨p,hp,hpGraph⟩ := exists_node_map hM hA.probes_map hs.1
  obtain ⟨hAdj,hExit⟩ := mapped_relations hA hB hw hz hzw hf hPres hb hd hFactor hTerminal hs hc hpGraph
  obtain ⟨L,hL,hLaw⟩ := presentation_lift hB hw hz hzw hJ hMul ht hp hUnit hAssoc hAdj hExit
  have hOld : NodeMap ON L t := by
    intro x y
    constructor
    · intro hy
      obtain ⟨ox,hox,_⟩ := hB.old_map.1.2 x (function_input ht.1.1 hy)
      exact ⟨ox,hox,(hLaw.1.2.2 x ox y ((hB.old_graph x ox).mp hox)).mpr hy⟩
    · rintro ⟨ox,hox,hy⟩
      exact (hLaw.1.2.2 x ox y ((hB.old_graph x ox).mp hox)).mp hy
  have hNew : NodeMap H L s := by
    obtain ⟨comp,hcomp,hcompGraph⟩ := exists_node_map hM hH.1 hL.1
    have he : comp = s := by
      apply presentation_ext hA hw hz hzw hMul hcomp hs.1
        (composition_preserves hcompGraph hH.2.2 hL.2.2) hs.2.2
      · intro x q hx y z hy hsz
        obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx.1
        obtain ⟨Q,hQ,_⟩ := hB.old_map.1.2 fx (hf.2 x fx hfx)
        have hO := (hA.old_graph x q).mpr hx
        have hHQ := hEnd.1 x fx q Q hfx hO hQ
        have hLy := (composition_value hH.1 hcompGraph hHQ).mp hy
        have hTy := (hLaw.1.2.2 fx Q y ((hB.old_graph fx Q).mp hQ)).mp hLy
        exact function_unique hs.1.1 ((hc x q fx y hO hfx).mpr hTy) hsz
      · intro i q hq y z hy hsz
        obtain ⟨Q,hQ,_⟩ := hB.probes_map.1.2 i (function_input hA.probes_map.1 hq)
        have hLy := (composition_value hH.1 hcompGraph (hEnd.2 i q Q hq hQ)).mp hy
        have hpy := (hLaw.2 i Q y hQ).mp hLy
        exact function_unique hs.1.1 ((composition_value hA.probes_map hpGraph hq).mp hpy) hsz
    exact he ▸ hcompGraph
  refine ⟨L,hL,hNew,hOld,?_⟩
  intro R hR hRN hRO
  apply presentation_ext hB hw hz hzw hMul hR.1 hL.1 hR.2.2 hL.2.2
  · intro x q hx y z hy hzv
    have hq := (hB.old_graph x q).mpr hx
    exact function_unique ht.1.1 ((composition_value hB.old_map hRO hq).mpr hy)
      ((composition_value hB.old_map hOld hq).mpr hzv)
  · intro i Q hQ y z hy hzv
    obtain ⟨q,hq,_⟩ := hA.probes_map.1.2 i (function_input hB.probes_map.1 hQ)
    have hHQ := hEnd.2 i q Q hq hQ
    exact function_unique hs.1.1 ((composition_value hH.1 hRN hHQ).mpr hy)
      ((composition_value hH.1 hNew hHQ).mpr hzv)

/-- The same actual conservative simulation is constructed before proving its
pushout property. There is no assumed lift or assumed universal property. -/
theorem exists_pushout
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    {g : M.Carrier .set}
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hAlphabet : ConstructionProbeAlphabetMap.AlphabetSimulation S SN act actN E EN f g)
    (hb : PureKuratowski.PairMember M b bN f) (hOne : PureKuratowski.PairMember M e eN f)
    (hd : PureKuratowski.PairMember M d dN f)
    (hFactor : FactorMap factor factorN f) (hTerminal : TerminalMap terminal terminalN f)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hOldA : Conservative D W mul G O) (hOldB : Conservative N WN mulN GN ON)
    (hLetters : ConstructionProbeLettersMap.Graph S projection projectionN f g) :
    ∃ H, ConstructionProbeWordTransport.WordGraph w D S SN f g W H ∧ Hom W WN G GN unit unitN H ∧
      Conservative W WN G GN H ∧ EndpointLaws f H O ON P PN ∧
      IsPushout N W WN mulN G GN eN unit unitN O f H ON := by
  obtain ⟨H,hGraph,hProd,hUnit,hCon,hEnd⟩ := ConstructionProbeSimulation.exists_simulation hM hw hz hzw
    hA.monoid hB.monoid hA.alphabet hB.alphabet hf hPres hAlphabet hb hOne hA.word hB.word
    hA.multiplication hB.multiplication hA.old_unit hB.old_unit hA.old_graph hB.old_graph hJ hOldA hOldB
    hA.generators_map hA.generators hB.generators hLetters hA.probes hB.probes
  have hHom : Hom W WN G GN unit unitN H := ⟨hCon.1.1,hUnit,hProd⟩
  exact ⟨H,hGraph,hHom,hCon,hEnd,simulation_pushout hA hB hw hz hzw hf.1.1 hPres hb hd hFactor hTerminal hHom hEnd⟩

end Actual
end PPAC.Migration.ConstructionProbePushout
