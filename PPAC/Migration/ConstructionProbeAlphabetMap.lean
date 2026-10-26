/- Pinned ProbePresentations.Path.lettersMap_act/exit/inCone_iff/alphabetSimulation.
Conservative.factors and injectivity yield exact old-factor reflection, then the
existing finite-stage cone criterion supplies the source cone equivalence. -/
import PPAC.Migration.ConstructionProbeLettersMapSyntax
import PPAC.Migration.ConstructionProbeCones

namespace PPAC.Migration.ConstructionProbeAlphabetMap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePath ConstructionProbeTransitions ConstructionProbeLetters
open ConstructionProbeMappedPath ConstructionProbeLettersMap
open ConstructionProbeLettersMapSyntax (RepresentativeLaw)
open ConstructionProbeAction (ActionTable representative)
open ConstructionProbeTarget (TargetGraph)
open ConstructionProbeAlphabet (ExitGraph InCone)
open ConstructionProbeCones (FiniteCone inCone_letter_iff)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeLiftHom (PreservesProducts)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The precise factors field of the source Conservative map, on internal carriers.
The other Conservative fields are not replaced by this weaker component. -/
def FactorConservation (N mulN f : M.Carrier .set) : Prop := ∀ x y z fx fy,
  PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
  (Project.FirstOrderSemantics.reduct M).mem z N → Product mulN fx z fy →
    ∃ t, PureKuratowski.PairMember M t z f

def DivisionReflection (D N mul mulN f : M.Carrier .set) : Prop := ∀ x y fx fy,
  PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
    (Divides N mulN fx fy ↔ Divides D mul x y)

/-- Pinned Conservative.factor_eq: reflect the particular factor, not just
existence of some unrelated source divisor. -/
theorem factor_eq {D N mul mulN e eN f x y z fx fy : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hf : Injection D N f) (hPres : PreservesProducts mul mulN f)
    (hFactors : FactorConservation N mulN f)
    (hx : PureKuratowski.PairMember M x fx f) (hy : PureKuratowski.PairMember M y fy f)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z N) (hprod : Product mulN fx z fy) :
    ∃ t, PureKuratowski.PairMember M t z f ∧ Product mul x t y := by
  obtain ⟨t,ht⟩ := hFactors x y z fx fy hx hy hz hprod
  obtain ⟨v,hv,hxv⟩ := (hm.2.1 x (function_input hf.1.1 hx)).1 t (function_input hf.1.1 ht)
  obtain ⟨fv,hfv,_⟩ := hf.1.1.2 v hv
  have he := (hmN.2.1 fx (hf.1.2 x fx hx)).2.1 z fv fy hz
    (hPres x t v fx z fv hxv hx ht hfv) hprod
  have hvy := hf.2 v y fy (he ▸ hfv) hy
  exact ⟨t,ht,hvy ▸ hxv⟩

theorem division_reflection {D N mul mulN e eN f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hf : Injection D N f) (hPres : PreservesProducts mul mulN f)
    (hFactors : FactorConservation N mulN f) : DivisionReflection D N mul mulN f := by
  intro x y fx fy hx hy
  constructor
  · rintro ⟨z,hz,hprod⟩
    obtain ⟨t,ht,hxt⟩ := factor_eq hm hmN hf hPres hFactors hx hy hz hprod
    exact ⟨t,function_input hf.1.1 ht,hxt⟩
  · rintro ⟨t,ht,hxt⟩
    obtain ⟨ft,hft,_⟩ := hf.1.1.2 t ht
    exact ⟨ft,hf.1.2 t ft hft,hPres x t y fx ft fy hxt hx hft hy⟩

def ActionMap (A AN f g : M.Carrier .set) : Prop := ∀ x s t fx gs gt,
  Product A x s t → PureKuratowski.PairMember M x fx f →
  PureKuratowski.PairMember M s gs g → PureKuratowski.PairMember M t gt g → Product AN fx gs gt

def ExitMap (E EN f g : M.Carrier .set) : Prop := ∀ s z gs fz,
  PureKuratowski.PairMember M s z E → PureKuratowski.PairMember M s gs g →
  PureKuratowski.PairMember M z fz f → PureKuratowski.PairMember M gs fz EN

def ConeMap (S SN A AN f g : M.Carrier .set) : Prop := ∀ x s fx gs,
  PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M s gs g →
    (InCone SN AN fx gs ↔ InCone S A x s)

def AlphabetSimulation (S SN A AN E EN f g : M.Carrier .set) : Prop :=
  Injection S SN g ∧ ActionMap A AN f g ∧ ExitMap E EN f g ∧ ConeMap S SN A AN f g

theorem lettersMap_act {D N mul mulN e projection projectionN A AN f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f)
    (hRep : RepresentativeLaw projection projectionN f g)
    (hA : ActionTable D mul projection A) (hAN : ActionTable N mulN projectionN AN) : ActionMap A AN f g := by
  intro x s t fx gs gt hact hfx hgs hgt
  obtain ⟨hx,i,y,xy,hy,hys,hxy,hxyt⟩ := (hA x s t).mp hact
  obtain ⟨fy,hfy,_⟩ := hf.1.2 y hy
  obtain ⟨fxy,hfxy,_⟩ := hf.1.2 xy (product_closed hm hx hy hxy)
  exact (hAN fx gs gt).mpr ⟨hf.2 x fx hfx,i,fy,fxy,hf.2 y fy hfy,
    (hRep i y fy s gs hys hfy).mp hgs,hPres x y xy fx fy fxy hxy hfx hfy hfxy,
    (hRep i xy fxy t gt hxyt hfxy).mp hgt⟩

theorem lettersMap_exit {w D N mul mulN e projection projectionN T U K KN d fd E EN f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f)
    (hRep : RepresentativeLaw projection projectionN f g) (hT : MapsTo w D T) (hTm : TerminalMap T U f)
    (hK : TargetGraph D mul projection T K) (hKN : TargetGraph N mulN projectionN U KN)
    (hE : ExitGraph mul K d E) (hEN : ExitGraph mulN KN fd EN)
    (hdf : PureKuratowski.PairMember M d fd f) : ExitMap E EN f g := by
  intro s z gs fz hsz hgs hfz
  obtain ⟨v,hsv,hvdz⟩ := (hE s z).mp hsz
  obtain ⟨i,x,t,hx,hxs,hit,hxtv⟩ := (hK s v).mp hsv
  obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
  obtain ⟨ft,hft,_⟩ := hf.1.2 t (hT.2 i t hit)
  obtain ⟨fv,hfv,_⟩ := hf.1.2 v (product_closed hm hx (hT.2 i t hit) hxtv)
  have hTarget := (hKN gs fv).mpr ⟨i,fx,ft,hf.2 x fx hfx,
    (hRep i x fx s gs hxs hfx).mp hgs,hTm i t ft hit hft,
    hPres x t v fx ft fv hxtv hfx hft hfv⟩
  exact (hEN gs fz).mpr ⟨fv,hTarget,hPres v d z fv fd fz hvdz hfv hdf hfz⟩

theorem finiteCone_iff {w D N mul mulN e eN zero a fa node mapped F G f x y fx fy i : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hp : Path w D mul e zero a node) (hpN : Path w N mulN eN zero fa mapped)
    (hF : FactorTable w D mul node F) (hG : FactorTable w N mulN mapped G)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hDiv : DivisionReflection D N mul mulN f)
    (hx : PureKuratowski.PairMember M x fx f) (hy : PureKuratowski.PairMember M y fy f) :
    FiniteCone w N mulN G fx i fy ↔ FiniteCone w D mul F x i y := by
  constructor
  · rintro ⟨j,z,hj,htrans,hdiv⟩
    have hcopy := htrans
    obtain ⟨_,r,hr,_⟩ := hcopy
    obtain ⟨hi,_,hij,_⟩ := (hG i j r).mp hr
    obtain ⟨v,hv,hyv⟩ := transition_total hm hp hF hi hj hij (function_input hf.1 hy)
    obtain ⟨fv,hfv,_⟩ := hf.1.2 v hv
    have he := transition_unique hmN hpN hG (map_transition hf hF hPres hmap hy hfv hyv) htrans
    exact ⟨j,v,hj,hyv,(hDiv x v fx fv hx hfv).mp (he.symm ▸ hdiv)⟩
  · rintro ⟨j,v,hj,hyv,hdiv⟩
    obtain ⟨fv,hfv,_⟩ := hf.1.2 v (transition_closed hm hF hyv)
    exact ⟨j,fv,hj,map_transition hf hF hPres hmap hy hfv hyv,(hDiv x v fx fv hx hfv).mpr hdiv⟩

theorem lettersMap_inCone_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N mul mulN e eN zero a fa node mapped F G C CN S SN projection projectionN A AN f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hp : Path w D mul e zero a node) (hpN : Path w N mulN eN zero fa mapped)
    (hF : FactorTable w D mul node F) (hG : FactorTable w N mulN mapped G)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hDiv : DivisionReflection D N mul mulN f)
    (hC : Representatives w D C) (hL : Letters w D mul F C S) (hproj : MapsTo C S projection)
    (hProjection : Projection w D mul F C projection) (hEq : EqualityLaw w D mul F projection)
    (hCN : Representatives w N CN) (hprojN : MapsTo CN SN projectionN) (hEqN : EqualityLaw w N mulN G projectionN)
    (hMeets : MeetsLaws w D mul F) (hMeetsN : MeetsLaws w N mulN G)
    (hA : ActionTable D mul projection A) (hAN : ActionTable N mulN projectionN AN)
    (hgm : MapsTo S SN g) (hRep : RepresentativeLaw projection projectionN f g) : ConeMap S SN A AN f g := by
  intro x s fx gs hfx hgs
  obtain ⟨i,y,_,_,hys⟩ := representative hC hL hProjection (function_input hgm.1 hgs)
  have hy := (ConstructionProbeAction.projected_indices hC hproj hys).2
  obtain ⟨fy,hfy,_⟩ := hf.1.2 y hy
  have hfgs := (hRep i y fy s gs hys hfy).mp hgs
  exact (inCone_letter_iff hM hmN hG hCN hprojN hEqN hMeetsN hAN (hf.2 x fx hfx) hfgs).trans
    ((finiteCone_iff hm hmN hp hpN hF hG hf hPres hmap hDiv hfx hfy).trans
      (inCone_letter_iff hM hm hF hC hproj hEq hMeets hA (function_input hf.1 hfx) hys).symm)

theorem exists_alphabet_simulation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N mul mulN e eN zero a fa node mapped F G C CN S SN projection projectionN f A AN T U K KN d fd E EN : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hp : Path w D mul e zero a node) (hpN : Path w N mulN eN zero fa mapped)
    (hF : FactorTable w D mul node F) (hG : FactorTable w N mulN mapped G)
    (hf : Injection D N f) (hPres : PreservesProducts mul mulN f) (hFactors : FactorConservation N mulN f)
    (hmap : FactorMap F G f) (hC : Representatives w D C) (hL : Letters w D mul F C S)
    (hproj : MapsTo C S projection) (hProjection : Projection w D mul F C projection)
    (hEq : EqualityLaw w D mul F projection) (hCN : Representatives w N CN)
    (hprojN : MapsTo CN SN projectionN) (hEqN : EqualityLaw w N mulN G projectionN)
    (hMeets : MeetsLaws w D mul F) (hMeetsN : MeetsLaws w N mulN G)
    (hA : ActionTable D mul projection A) (hAN : ActionTable N mulN projectionN AN)
    (hT : MapsTo w D T) (hTm : TerminalMap T U f)
    (hK : TargetGraph D mul projection T K) (hKN : TargetGraph N mulN projectionN U KN)
    (hE : ExitGraph mul K d E) (hEN : ExitGraph mulN KN fd EN)
    (hdf : PureKuratowski.PairMember M d fd f) :
    ∃ g, Graph S projection projectionN f g ∧ RepresentativeLaw projection projectionN f g ∧
      AlphabetSimulation S SN A AN E EN f g := by
  obtain ⟨g,hgm,hg⟩ := exists_graph hM hm hf.1 hF hPres hmap hC hL hProjection hEq hCN hprojN hEqN
  have hRep : RepresentativeLaw projection projectionN f g := fun _ _ _ _ _ hxs hfx =>
    map_letter hM hm hf.1 hF hPres hmap hC hproj hEq hCN hprojN hEqN hg hxs hfx
  exact ⟨g,hg,hRep,graph_injective hm hmN hp hpN hF hG hf hPres hmap hEq hEqN hgm hg,
    lettersMap_act hm hf.1 hPres hRep hA hAN,
    lettersMap_exit hm hf.1 hPres hRep hT hTm hK hKN hE hEN hdf,
    lettersMap_inCone_iff hM hm hmN hp hpN hF hG hf.1 hPres hmap
      (division_reflection hm hmN hf hPres hFactors) hC hL hproj hProjection hEq hCN hprojN hEqN
      hMeets hMeetsN hA hAN hgm hRep⟩

end PPAC.Migration.ConstructionProbeAlphabetMap
