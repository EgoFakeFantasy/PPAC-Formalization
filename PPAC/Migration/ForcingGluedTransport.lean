/- Pinned QuotientTransport.ReindexIso.fiberEquiv_arrow/gluedEquiv/
gluedEquiv_toGlued:252-293. Actual root-fiber construction and whole-component
naturality, retaining distinct source and target Systems. -/
import PPAC.Migration.ForcingComponentMove
import PPAC.Migration.ForcingReindexSystem

namespace PPAC.Migration.ForcingGluedTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (CompositionGraph Permutation)
open ConstructionComponentCarrier (Code EncodedVertex)
open ConstructionComponentCofinal (EncodedArrow EncodedCommon)
open ForcingComponentFibers (VertexFiber ArrowMap)
open ForcingComponentGluing (ToGlued AllFiberMaps Commuting)
open ForcingComponentMove (Move)
open ForcingEligibleRestriction (Restricts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def FiberMove (D mul pi objects maps targets targetMaps apps v V X Y f : M.Carrier .set) : Prop :=
  ∃ r i U R Or OR a, Code v r i U ∧ Code V R i U ∧ CompositionGraph D pi r R ∧
    PureKuratowski.PairMember M r Or objects ∧ PureKuratowski.PairMember M R OR targets ∧
    PureKuratowski.PairMember M r a apps ∧ ForcingSystemFibers.Fiber D mul objects maps r Or i U X ∧
    ForcingSystemFibers.Fiber D mul targets targetMaps R OR i U Y ∧ Restricts f a X ∧
    Injection X Y f ∧ ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Y →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x y f

theorem fiberMove_data {D mul pi objects maps targets targetMaps apps v V X Y f : M.Carrier .set}
    (h : FiberMove D mul pi objects maps targets targetMaps apps v V X Y f) :
    Injection X Y f ∧ ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Y →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x y f := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hInj,hOnto⟩ := h
  exact ⟨hInj,hOnto⟩

theorem exists_fiberMove (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q pi diagrams appImage objects maps targets targetMaps apps v V X Y : M.Carrier .set}
    (hAppMap : MapsTo diagrams appImage apps) (hApps : ForcingReindexSystem.Apps D pi objects targets apps)
    (hPres : ForcingReindexSystem.PreservesAvailability D mul pi objects maps targets targetMaps apps)
    (hMove : Move D I mul q pi v V) (hX : VertexFiber D mul objects maps v X)
    (hY : VertexFiber D mul targets targetMaps V Y) :
    ∃ f, FiberMove D mul pi objects maps targets targetMaps apps v V X Y f := by
  obtain ⟨r,i,U,R,hv,hV,_,_,hComp⟩ := hMove
  obtain ⟨r',i',U',Or,hv',hr,hX⟩ := hX
  obtain ⟨R',j',W',OR,hV',hR,hY⟩ := hY
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hV hV'
  obtain ⟨a,ha,_,_⟩ := hApps r R Or OR hComp hr hR
  obtain ⟨f,hf,hRestricts,hOnto⟩ := ForcingReindexSystem.fiber_bijection hM hAppMap hApps hPres hComp hr hR ha hX hY
  exact ⟨f,r,i,U,R,Or,OR,a,hv,hV,hComp,hr,hR,ha,hX,hY,hRestricts,hf,hOnto⟩

theorem fiber_natural {D mul pi objects maps targets targetMaps apps v V w W X XT Y YT a b f g x y Xv Yv : M.Carrier .set}
    (hNatural : ForcingReindexSystem.Natural D pi maps targetMaps apps)
    (hA : FiberMove D mul pi objects maps targets targetMaps apps v V X XT a)
    (hB : FiberMove D mul pi objects maps targets targetMaps apps w W Y YT b)
    (hf : ArrowMap maps v w X Y f) (hg : ArrowMap targetMaps V W XT YT g)
    (hxy : PureKuratowski.PairMember M y x f) (hxX : PureKuratowski.PairMember M x Xv a)
    (hyY : PureKuratowski.PairMember M y Yv b) : PureKuratowski.PairMember M Yv Xv g := by
  have hbData := fiberMove_data hB
  obtain ⟨r,i,U,R,Or,OR,ar,hv,hV,hR,_,_,har,_,_,hAR,_,_⟩ := hA
  obtain ⟨s,j,T,S,Os,OS,bs,hw,hW,hS,_,_,hbs,_,_,hBR,_,_⟩ := hB
  obtain ⟨r',i',U',s',j',T',z,f0,hv',hw',hz,hf0,hFR,_,_⟩ := hf
  obtain ⟨R',iT,UT,S',jT,TT,Z,g0,hV',hW',hZ,hg0,hGR,_,_⟩ := hg
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hV hV'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hW hW'
  exact (hGR Yv Xv).mpr ⟨hNatural r s R S z Z f0 g0 ar bs y x Yv Xv hR hS hz hZ hf0 hg0 har hbs
    ((hFR y x).mp hxy).1 ((hBR y Yv).mp hyY).1 ((hAR x Xv).mp hxX).1,hbData.1.1.2 y Yv hyY⟩

/-- Exactly the source root-fiber composite c ∘ f ∘ b⁻¹, as a set graph. -/
def RootMap (b f c g : M.Carrier .set) : Prop := ∀ C E,
  PureKuratowski.PairMember M C E g ↔ ∃ x y,
    PureKuratowski.PairMember M x C b ∧ PureKuratowski.PairMember M x y f ∧ PureKuratowski.PairMember M y E c

def rootMap {m : Nat} (b f c g : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ 1 0))
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge b.succ.succ.succ.succ 1 3))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ 1 0))
        (ProjectSyntax.encode id (Source.SetLanguage.edge c.succ.succ.succ.succ 0 2))))))))

theorem rootMap_freeClosed {m : Nat} (b f c g : Fin m) : (rootMap b f c g).FreeClosed := by
  simp -implicitDefEqProofs [rootMap,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem rootMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (b f c g : Fin m) :
    Project.Formula.satisfies env (rootMap b f c g) ↔ RootMap (env.bound b) (env.bound f) (env.bound c) (env.bound g) := by
  simp only [rootMap,RootMap,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem exists_rootMap (hM : FirstOrder.Theory.Models M nativeZF)
    {X Y Q Z b f c : M.Carrier .set}
    (hb : Injection X Q b) (hbOnto : ∀ C, (Project.FirstOrderSemantics.reduct M).mem C Q →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x C b)
    (hf : Injection X Y f) (hfOnto : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Y →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x y f)
    (hc : Injection Y Z c) (hcOnto : ∀ E, (Project.FirstOrderSemantics.reduct M).mem E Z →
      ∃ y, (Project.FirstOrderSemantics.reduct M).mem y Y ∧ PureKuratowski.PairMember M y E c) :
    ∃ g, Injection Q Z g ∧ RootMap b f c g ∧
      ∀ E, (Project.FirstOrderSemantics.reduct M).mem E Z →
        ∃ C, (Project.FirstOrderSemantics.reduct M).mem C Q ∧ PureKuratowski.PairMember M C E g := by
  let schema : Project.BinarySchema 3 := {
    body := .existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 4 1 3))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 5 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge 6 0 2)))))
    freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases b (Fin.cases f (fun _ => c)), free := fun _ => Q }
  have he C E : schema.denote env C E ↔ ∃ x y, PureKuratowski.PairMember M x C b ∧
      PureKuratowski.PairMember M x y f ∧ PureKuratowski.PairMember M y E c := by
    simp only [schema,env,Project.BinarySchema.denote,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
    rfl
  have ht : ∀ C, (Project.FirstOrderSemantics.reduct M).mem C Q → ∃ E, schema.denote env C E := by
    intro C hC
    obtain ⟨x,hx,hxC⟩ := hbOnto C hC
    obtain ⟨y,hxy,_⟩ := hf.1.1.2 x hx
    obtain ⟨E,hyE,_⟩ := hc.1.1.2 y (hf.1.2 x y hxy)
    exact ⟨E,(he C E).mpr ⟨x,y,hxC,hxy,hyE⟩⟩
  have hu : ∀ C E F, schema.denote env C E → schema.denote env C F → E = F := by
    intro C E F hE hF
    obtain ⟨x,y,hxC,hxy,hyE⟩ := (he C E).mp hE
    obtain ⟨x',y',hxC',hxy',hyF⟩ := (he C F).mp hF
    have ex := hb.2 x x' C hxC hxC'; subst x'
    have ey := ForcingConditionGraphs.function_unique hf.1.1 hxy hxy'; subst y'
    exact ForcingConditionGraphs.function_unique hc.1.1 hyE hyF
  obtain ⟨g,hg,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun C _ E F hE hF => hu C E F hE hF)
    (fun C E _ hE => by obtain ⟨_,y,_,_,hyE⟩ := (he C E).mp hE; exact hc.1.2 y E hyE)
  have hRoot : RootMap b f c g := by
    intro C E
    constructor
    · intro hCE
      exact (he C E).mp ((hEdge C E).mp hCE).2
    · intro h
      have hc := h
      obtain ⟨x,_,hxC,_,_⟩ := hc
      exact (hEdge C E).mpr ⟨hb.1.2 x C hxC,(he C E).mpr h⟩
  refine ⟨g,⟨(ForcingSupportSize.native_mapsTo hM Q Z g).mpr hg,?_⟩,hRoot,?_⟩
  · intro C E F hCF hEF
    obtain ⟨x,y,hxC,hxy,hyF⟩ := (hRoot C F).mp hCF
    obtain ⟨x',y',hxE,hxy',hyF'⟩ := (hRoot E F).mp hEF
    have ey := hc.2 y y' F hyF hyF'; subst y'
    have ex := hf.2 x x' y hxy hxy'; subst x'
    exact ForcingConditionGraphs.function_unique hb.1.1 hxC hxE
  · intro E hE
    obtain ⟨y,hy,hyE⟩ := hcOnto E hE
    obtain ⟨x,hx,hxy⟩ := hfOnto y hy
    obtain ⟨C,hxC,_⟩ := hb.1.1.2 x hx
    exact ⟨C,hb.1.2 x C hxC,(hRoot C E).mpr ⟨x,y,hxC,hxy,hyE⟩⟩


theorem glued_natural (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q pi diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps
      appImage apps v V X XT fRoot Q Z pr prT bRoot cRoot phi w W Y YT f bw cw x y C E : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hTargets : MapsTo diagrams targetImage targets)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hTargetMaps : MapsTo S targetMapImage targetMaps)
    (hSys : ForcingEligibleSystem.System D objects maps) (hTSys : ForcingEligibleSystem.System D targets targetMaps)
    (hAppMap : MapsTo diagrams appImage apps) (hApps : ForcingReindexSystem.Apps D pi objects targets apps)
    (hPres : ForcingReindexSystem.PreservesAvailability D mul pi objects maps targets targetMaps apps)
    (hNatural : ForcingReindexSystem.Natural D pi maps targetMaps apps)
    (hv : Move D I mul q pi v V) (hX : VertexFiber D mul objects maps v X)
    (hXT : VertexFiber D mul targets targetMaps V XT)
    (hfRoot : FiberMove D mul pi objects maps targets targetMaps apps v V X XT fRoot)
    (hAll : AllFiberMaps D I mul q objects maps v Q pr) (hComm : Commuting D I mul q objects maps Q pr)
    (hAllT : AllFiberMaps D I mul q targets targetMaps V Z prT) (hCommT : Commuting D I mul q targets targetMaps Z prT)
    (hbRoot : ToGlued v X Q pr bRoot) (hcRoot : ToGlued V XT Z prT cRoot) (hRoot : RootMap bRoot fRoot cRoot phi)
    (hCommon : EncodedCommon D I mul q v w) (hw : Move D I mul q pi w W)
    (hY : VertexFiber D mul objects maps w Y) (hYT : VertexFiber D mul targets targetMaps W YT)
    (hf : FiberMove D mul pi objects maps targets targetMaps apps w W Y YT f)
    (hbw : ToGlued w Y Q pr bw) (hcw : ToGlued W YT Z prT cw)
    (hxC : PureKuratowski.PairMember M x C bw) (hxy : PureKuratowski.PairMember M x y f)
    (hyE : PureKuratowski.PairMember M y E cw) : PureKuratowski.PairMember M C E phi := by
  obtain ⟨r,i,U,s,j,T,hvCode,hwCode,hr,hs,t,k,L,n,m,ht,hn,hmw⟩ := hCommon
  obtain ⟨u,huCode⟩ := ConstructionComponentCarrier.code_total hM t k L
  have hu : EncodedVertex D I mul q u := ⟨t,k,L,huCode,ht⟩
  have hav : EncodedArrow D I mul q v u n := ⟨r,i,U,t,k,L,hvCode,huCode,hr,ht,hn⟩
  have haw : EncodedArrow D I mul q w u m := ⟨s,j,T,t,k,L,hwCode,huCode,hs,ht,hmw⟩
  obtain ⟨UT,huMove⟩ := ForcingComponentMove.exists_move hM hp hFix hu
  obtain ⟨F,hF⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj hu
  obtain ⟨FT,hFT⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hTargets (ForcingComponentMove.target_vertex huMove)
  obtain ⟨fu,hfu⟩ := exists_fiberMove hM hAppMap hApps hPres huMove hF hFT
  obtain ⟨a,ha⟩ := ForcingComponentFibers.exists_arrowMap hM hm hJ hDiagrams hObj hS hMaps hSys hav hX hF
  obtain ⟨b,hb⟩ := ForcingComponentFibers.exists_arrowMap hM hm hJ hDiagrams hObj hS hMaps hSys haw hY hF
  have havT := ForcingComponentMove.move_arrow hv huMove hav
  have hawT := ForcingComponentMove.move_arrow hw huMove haw
  obtain ⟨aT,haT⟩ := ForcingComponentFibers.exists_arrowMap hM hm hJ hDiagrams hTargets hS hTargetMaps hTSys havT hXT hFT
  obtain ⟨bT,hbT⟩ := ForcingComponentFibers.exists_arrowMap hM hm hJ hDiagrams hTargets hS hTargetMaps hTSys hawT hYT hFT
  have hx := ForcingConditionGraphs.function_input hbw.1.1 hxC
  obtain ⟨z,hz,hzx⟩ := (ForcingComponentMatches.map_bijective hb).2 x hx
  obtain ⟨x0,hzx0,_⟩ := (ForcingComponentMatches.map_bijective ha).1.1.1.2 z hz
  have hx0 := (ForcingComponentMatches.map_bijective ha).1.1.2 z x0 hzx0
  obtain ⟨x0T,hx0T,_⟩ := (fiberMove_data hfRoot).1.1.1.2 x0 hx0
  obtain ⟨zT,hzT,_⟩ := (fiberMove_data hfu).1.1.1.2 z hz
  have hzaT := fiber_natural hNatural hfRoot hfu ha haT hzx0 hx0T hzT
  have hzbT := fiber_natural hNatural hf hfu hb hbT hzx hxy hzT
  have hvu := ForcingComponentMatches.arrow_common hav (ForcingComponentMatches.arrow_id hm hu)
  have hvuT := ForcingComponentMove.move_common hM hp hFix hv huMove hvu
  obtain ⟨bu,hbu,_,_⟩ := hAll u F hvu hF
  obtain ⟨cu,hcu,_,_⟩ := hAllT UT FT hvuT hFT
  obtain ⟨C0,hC0,_⟩ := hbRoot.1.1.2 x0 hx0
  obtain ⟨Cu,hCu,_⟩ := hbu.1.1.2 z hz
  have hC0u := hComm v u X F n a bRoot bu x0 z C0 Cu hX hF hav ha hbRoot hbu hzx0 hC0 hCu
  have hCuC := hComm w u Y F m b bw bu x z C Cu hY hF haw hb hbw hbu hzx hxC hCu
  have hCeq : C0 = C := hC0u.trans hCuC.symm
  obtain ⟨E0,hE0,_⟩ := hcRoot.1.1.2 x0T ((fiberMove_data hfRoot).1.1.2 x0 x0T hx0T)
  obtain ⟨Eu,hEu,_⟩ := hcu.1.1.2 zT ((fiberMove_data hfu).1.1.2 z zT hzT)
  have hE0u := hCommT V UT XT FT n aT cRoot cu x0T zT E0 Eu hXT hFT havT haT hcRoot hcu hzaT hE0 hEu
  have hEuE := hCommT W UT YT FT m bT cw cu y zT E Eu hYT hFT hawT hbT hcw hcu hzbT hyE hEu
  have hEeq : E0 = E := hE0u.trans hEuE.symm
  exact (hRoot C E).mpr ⟨x0,x0T,hCeq ▸ hC0,hx0T,hEeq ▸ hE0⟩


/-- Existing entire-component quotient, with its actual projection and laws. -/
def Gluing (D I mul q objects maps v P Q pr : M.Carrier .set) : Prop :=
  ForcingComponentGluing.Component D I mul q objects maps v P ∧ MapsTo P Q pr ∧
  ForcingComponentGluing.Classes D I mul q objects maps P Q ∧
  ForcingComponentGluing.Projection D I mul q objects maps P pr ∧
  AllFiberMaps D I mul q objects maps v Q pr ∧ Commuting D I mul q objects maps Q pr

theorem exists_gluing (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps) :
    ∃ P Q pr, Gluing D I mul q objects maps v P Q pr := by
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM D I mul q
  obtain ⟨image,fibers,hFibers,hFamily⟩ := ForcingComponentFibers.exists_family hM hDiagrams hObj hVertices
  obtain ⟨A,hA⟩ := ForcingComponentMatches.exists_carrier hM hVertices hFibers hFamily
  obtain ⟨P,hP⟩ := ForcingComponentGluing.exists_component hM hA (root := v)
  obtain ⟨Q,pr,hpr,hQ,hProjection⟩ := ForcingComponentGluing.exists_quotient hM D I mul q objects maps P
  exact ⟨P,Q,pr,hP,hpr,hQ,hProjection,ForcingComponentGluing.gluing_laws hM hm hJ hDiagrams hObj hS hMaps hSys hP hpr hQ hProjection⟩

def Naturality (D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi : M.Carrier .set) : Prop :=
  ∀ w W Y YT f b c x y C E,
    EncodedCommon D I mul q v w → Move D I mul q pi w W →
    VertexFiber D mul objects maps w Y → VertexFiber D mul targets targetMaps W YT →
    FiberMove D mul pi objects maps targets targetMaps apps w W Y YT f →
    ToGlued w Y Q pr b → ToGlued W YT Z prT c →
    PureKuratowski.PairMember M x C b → PureKuratowski.PairMember M x y f →
    PureKuratowski.PairMember M y E c → PureKuratowski.PairMember M C E phi

def Transport (D I mul q pi objects maps targets targetMaps apps v : M.Carrier .set) : Prop :=
  ∃ V X XT P Q pr PT Z prT f b c phi,
    Move D I mul q pi v V ∧ VertexFiber D mul objects maps v X ∧ VertexFiber D mul targets targetMaps V XT ∧
    Gluing D I mul q objects maps v P Q pr ∧ Gluing D I mul q targets targetMaps V PT Z prT ∧
    FiberMove D mul pi objects maps targets targetMaps apps v V X XT f ∧
    ToGlued v X Q pr b ∧ ToGlued V XT Z prT c ∧ RootMap b f c phi ∧ Injection Q Z phi ∧
    (∀ E, (Project.FirstOrderSemantics.reduct M).mem E Z →
      ∃ C, (Project.FirstOrderSemantics.reduct M).mem C Q ∧ PureKuratowski.PairMember M C E phi) ∧
    Naturality D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi

theorem exists_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q pi diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hTargets : MapsTo diagrams targetImage targets)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hTargetMaps : MapsTo S targetMapImage targetMaps)
    (hSys : ForcingEligibleSystem.System D objects maps) (hTSys : ForcingEligibleSystem.System D targets targetMaps)
    (hAppMap : MapsTo diagrams appImage apps) (hApps : ForcingReindexSystem.Apps D pi objects targets apps)
    (hNatural : ForcingReindexSystem.Natural D pi maps targetMaps apps) (hv : EncodedVertex D I mul q v) :
    Transport D I mul q pi objects maps targets targetMaps apps v := by
  have hPres : ForcingReindexSystem.PreservesAvailability D mul pi objects maps targets targetMaps apps :=
    fun _ _ _ _ _ _ _ _ hR hr hT ha hxy hn => ForcingReindexSystem.available_iff hM hm hp hDiagrams hObj hTargets hS hMaps hTargetMaps hSys hTSys hAppMap hApps hNatural hR hr hT ha hxy hn
  obtain ⟨V,hMove⟩ := ForcingComponentMove.exists_move hM hp hFix hv
  have hV := ForcingComponentMove.target_vertex hMove
  obtain ⟨X,hX⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj hv
  obtain ⟨XT,hXT⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hTargets hV
  obtain ⟨f,hf⟩ := exists_fiberMove hM hAppMap hApps hPres hMove hX hXT
  obtain ⟨P,Q,pr,hG⟩ := exists_gluing hM hm hJ hDiagrams hObj hS hMaps hSys (q := q) (v := v)
  obtain ⟨PT,Z,prT,hGT⟩ := exists_gluing hM hm hJ hDiagrams hTargets hS hTargetMaps hTSys (q := q) (v := V)
  have hvv := ForcingComponentMatches.arrow_common (ForcingComponentMatches.arrow_id hm hv) (ForcingComponentMatches.arrow_id hm hv)
  have hVV := ForcingComponentMatches.arrow_common (ForcingComponentMatches.arrow_id hm hV) (ForcingComponentMatches.arrow_id hm hV)
  obtain ⟨b,hb,hbi,hbo⟩ := hG.2.2.2.2.1 v X hvv hX
  obtain ⟨c,hc,hci,hco⟩ := hGT.2.2.2.2.1 V XT hVV hXT
  obtain ⟨phi,hphi,hRoot,hOnto⟩ := exists_rootMap hM hbi hbo (fiberMove_data hf).1 (fiberMove_data hf).2 hci hco
  refine ⟨V,X,XT,P,Q,pr,PT,Z,prT,f,b,c,phi,hMove,hX,hXT,hG,hGT,hf,hb,hc,hRoot,hphi,hOnto,?_⟩
  intro w W Y YT f' b' c' x y C E hCommon hw hY hYT hf' hb' hc' hxC hxy hyE
  exact glued_natural hM hm hJ hp hFix hDiagrams hObj hTargets hS hMaps hTargetMaps hSys hTSys hAppMap hApps hPres hNatural
    hMove hX hXT hf hG.2.2.2.2.1 hG.2.2.2.2.2 hGT.2.2.2.2.1 hGT.2.2.2.2.2 hb hc hRoot
    hCommon hw hY hYT hf' hb' hc' hxC hxy hyE

def fiberMove {m : Nat} (D mul pi objects maps targets targetMaps apps v V X Y f : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionComponentCarrier.code v.succ.succ.succ.succ.succ.succ.succ 6 5 4) (.conj (ConstructionComponentCarrier.code V.succ.succ.succ.succ.succ.succ.succ 3 5 4) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ 6 3)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ.succ.succ.succ 6 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge targets.succ.succ.succ.succ.succ.succ.succ 3 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ.succ.succ.succ.succ.succ 6 0)) (.conj (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ 6 2 5 4 X.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ 3 1 5 4 Y.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw f.succ.succ.succ.succ.succ.succ.succ 0 X.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection f.succ.succ.succ.succ.succ.succ.succ X.succ.succ.succ.succ.succ.succ.succ Y.succ.succ.succ.succ.succ.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound Y.succ.succ.succ.succ.succ.succ.succ.succ)) (.existsE (.conj (.mem (.bound 0) (.bound X.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ 0 1)))))))))))))))))))))))

theorem fiberMove_freeClosed {m : Nat} (D mul pi objects maps targets targetMaps apps v V X Y f : Fin m) : (fiberMove D mul pi objects maps targets targetMaps apps v V X Y f).FreeClosed := by
  simp -implicitDefEqProofs [fiberMove,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.code_freeClosed]

theorem fiberMove_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul pi objects maps targets targetMaps apps v V X Y f : Fin m) :
    Project.Formula.satisfies env (fiberMove D mul pi objects maps targets targetMaps apps v V X Y f) ↔ FiberMove (env.bound D) (env.bound mul) (env.bound pi) (env.bound objects) (env.bound maps) (env.bound targets) (env.bound targetMaps) (env.bound apps) (env.bound v) (env.bound V) (env.bound X) (env.bound Y) (env.bound f) := by
  simp only [fiberMove,FiberMove,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingSystemFibers.fiber_semantics (M := M),ForcingEligibleRestriction.edgeLaw_semantics (M := M),ForcingSupportSize.injection_semantics (M := M)]
  rfl

def gluing {m : Nat} (D I mul q objects maps v P Q pr : Fin m) : Project.Formula 1 m :=
  (.conj (ForcingComponentGluing.component D I mul q objects maps v P) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr P Q)) (.conj (ForcingComponentGluing.classes D I mul q objects maps P Q) (.conj (ForcingComponentGluing.projection D I mul q objects maps P pr) (.conj (ForcingComponentGluing.allFiberMaps D I mul q objects maps v Q pr) (ForcingComponentGluing.commuting D I mul q objects maps Q pr))))))

theorem gluing_freeClosed {m : Nat} (D I mul q objects maps v P Q pr : Fin m) : (gluing D I mul q objects maps v P Q pr).FreeClosed := by
  simp -implicitDefEqProofs [gluing,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingComponentGluing.component_freeClosed,ForcingComponentGluing.classes_freeClosed,ForcingComponentGluing.projection_freeClosed,ForcingComponentGluing.allFiberMaps_freeClosed,ForcingComponentGluing.commuting_freeClosed]

theorem gluing_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps v P Q pr : Fin m) :
    Project.Formula.satisfies env (gluing D I mul q objects maps v P Q pr) ↔ Gluing (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound v) (env.bound P) (env.bound Q) (env.bound pr) := by
  simp only [gluing,Gluing,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingComponentGluing.component_semantics hM,ForcingComponentGluing.classes_semantics hM,ForcingComponentGluing.projection_semantics hM,ForcingComponentGluing.allFiberMaps_semantics hM,ForcingComponentGluing.commuting_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def naturality {m : Nat} (D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionComponentCofinal.encodedCommon D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10) (.imp (ForcingComponentMove.move D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 9) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 8) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 7) (.imp (fiberMove D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 9 8 7 6) (.imp (ForcingComponentGluing.toGlued 10 8 Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pr.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5) (.imp (ForcingComponentGluing.toGlued 9 7 Z.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ prT.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 5 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 6 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 4 2 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge phi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 0)))))))))))))))))))))))

theorem naturality_freeClosed {m : Nat} (D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi : Fin m) : (naturality D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi).FreeClosed := by
  simp -implicitDefEqProofs [naturality,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,ForcingComponentMove.move_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,fiberMove_freeClosed,ForcingComponentGluing.toGlued_freeClosed]

theorem naturality_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi : Fin m) :
    Project.Formula.satisfies env (naturality D I mul q pi objects maps targets targetMaps apps v Q Z pr prT phi) ↔ Naturality (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pi) (env.bound objects) (env.bound maps) (env.bound targets) (env.bound targetMaps) (env.bound apps) (env.bound v) (env.bound Q) (env.bound Z) (env.bound pr) (env.bound prT) (env.bound phi) := by
  simp only [naturality,Naturality,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ForcingComponentMove.move_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,fiberMove_semantics hM,ForcingComponentGluing.toGlued_semantics hM]
  rfl

def transport {m : Nat} (D I mul q pi objects maps targets targetMaps apps v : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ForcingComponentMove.move D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 10) (.conj (gluing D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7) (.conj (gluing D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 6 5 4) (.conj (fiberMove D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 11 10 3) (.conj (ForcingComponentGluing.toGlued v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 8 7 2) (.conj (ForcingComponentGluing.toGlued 12 10 5 4 1) (.conj (rootMap 2 3 1 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 8 5)) (.conj (.forallE (.imp (.mem (.bound 0) (.bound 6)) (.existsE (.conj (.mem (.bound 0) (.bound 10)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 1)))))) (naturality D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 5 7 4 0)))))))))))))))))))))))))

theorem transport_freeClosed {m : Nat} (D I mul q pi objects maps targets targetMaps apps v : Fin m) : (transport D I mul q pi objects maps targets targetMaps apps v).FreeClosed := by
  simp -implicitDefEqProofs [transport,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingComponentMove.move_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,gluing_freeClosed,fiberMove_freeClosed,ForcingComponentGluing.toGlued_freeClosed,rootMap_freeClosed,naturality_freeClosed]

theorem transport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pi objects maps targets targetMaps apps v : Fin m) :
    Project.Formula.satisfies env (transport D I mul q pi objects maps targets targetMaps apps v) ↔ Transport (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pi) (env.bound objects) (env.bound maps) (env.bound targets) (env.bound targetMaps) (env.bound apps) (env.bound v) := by
  simp only [transport,Transport,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingComponentMove.move_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,gluing_semantics hM,fiberMove_semantics hM,ForcingComponentGluing.toGlued_semantics hM,rootMap_semantics hM,ForcingSupportSize.injection_semantics (M := M),naturality_semantics hM]
  rfl

def constructionSentence {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D pi q q)) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targets diagrams targetImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targetMaps S targetMapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (.imp (ForcingEligibleSystem.system D targets targetMaps) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo apps diagrams appImage)) (.imp (ForcingReindexSystem.appsF D pi objects targets apps) (.imp (ForcingReindexSystem.natural D pi maps targetMaps apps) (.imp (ConstructionComponentCarrier.encodedVertex D I mul q v) (transport D I mul q pi objects maps targets targetMaps apps v)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingEligibleSystem.system_freeClosed,
      ForcingReindexSystem.appsF_freeClosed,ForcingReindexSystem.natural_freeClosed,ConstructionComponentCarrier.encodedVertex_freeClosed,transport_freeClosed]

theorem construction_models {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    ForcingReindexSystem.appsF_semantics hM,ForcingReindexSystem.natural_semantics hM,
    ConstructionComponentCarrier.encodedVertex_semantics hM,transport_semantics hM]
  exact exists_transport hM

theorem construction_kernel_certificate {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v hM)

end PPAC.Migration.ForcingGluedTransport
