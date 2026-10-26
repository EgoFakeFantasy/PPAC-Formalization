/- Pinned ProbePresentations.Path.lettersMap and injectivity.
Use the existing common-stage equality of actual set-coded quotients; transitions
are not assumed injective. The base-map factor equations are supplied by MappedPath. -/
import PPAC.Migration.ConstructionProbeMappedPathSyntax

namespace PPAC.Migration.ConstructionProbeLettersMap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeMappedPath ConstructionProbePath ConstructionProbeTransitions ConstructionProbeLetters
open ConstructionProbeAction (projected representative projected_indices projected_range)
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

theorem map_transition {w D N mul mulN node F G f i j x y fx fy : M.Carrier .set}
    (hf : MapsTo D N f) (hF : FactorTable w D mul node F)
    (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hx : PureKuratowski.PairMember M x fx f) (hy : PureKuratowski.PairMember M y fy f)
    (h : Transition D mul F i j x y) : Transition N mulN G i j fx fy := by
  obtain ⟨_,t,ht,hxt⟩ := h
  obtain ⟨_,_,_,ni,nj,_,_,htD,_⟩ := (hF i j t).mp ht
  obtain ⟨ft,hft,_⟩ := hf.1.2 t htD
  exact ⟨hf.2 x fx hx,ft,hmap i j t ft ht hft,hPres x t y fx ft fy hxt hx hft hy⟩

theorem map_meets {w D N mul mulN e node F G f i j x y fx fy : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : MapsTo D N f) (hF : FactorTable w D mul node F)
    (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hx : PureKuratowski.PairMember M x fx f) (hy : PureKuratowski.PairMember M y fy f)
    (h : Meets w D mul F i x j y) : Meets w N mulN G i fx j fy := by
  obtain ⟨k,z,hk,hxz,hyz⟩ := h
  obtain ⟨fz,hfz,_⟩ := hf.1.2 z (transition_closed hm hF hxz)
  exact ⟨k,fz,hk,map_transition hf hF hPres hmap hx hfz hxz,
    map_transition hf hF hPres hmap hy hfz hyz⟩

theorem reflect_meets {w D N mul mulN e eN zero a fa node mapped F G f i j x y fx fy : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hp : Path w D mul e zero a node) (hpN : Path w N mulN eN zero fa mapped)
    (hF : FactorTable w D mul node F) (hG : FactorTable w N mulN mapped G)
    (hf : Injection D N f) (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hx : PureKuratowski.PairMember M x fx f) (hy : PureKuratowski.PairMember M y fy f)
    (h : Meets w N mulN G i fx j fy) : Meets w D mul F i x j y := by
  obtain ⟨k,z,hk,hxz,hyz⟩ := h
  have hxz' := hxz
  have hyz' := hyz
  obtain ⟨_,ti,hti,_⟩ := hxz'
  obtain ⟨_,tj,htj,_⟩ := hyz'
  obtain ⟨hi,_,hik,_⟩ := (hG i k ti).mp hti
  obtain ⟨hj,_,hjk,_⟩ := (hG j k tj).mp htj
  obtain ⟨v,hv,hxv⟩ := transition_total hm hp hF hi hk hik (function_input hf.1.1 hx)
  obtain ⟨u,hu,hyu⟩ := transition_total hm hp hF hj hk hjk (function_input hf.1.1 hy)
  obtain ⟨fv,hfv,_⟩ := hf.1.1.2 v hv
  obtain ⟨fu,hfu,_⟩ := hf.1.1.2 u hu
  have hvz := transition_unique hmN hpN hG (map_transition hf.1 hF hPres hmap hx hfv hxv) hxz
  have huz := transition_unique hmN hpN hG (map_transition hf.1 hF hPres hmap hy hfu hyu) hyz
  have hvu := hf.2 v u fv hfv ((hvz.trans huz.symm).symm ▸ hfu)
  exact ⟨k,v,hk,hxv,hvu.symm ▸ hyu⟩

def Value (projection projectionN f s t : M.Carrier .set) : Prop := ∃ i x fx,
  Product projection i x s ∧ PureKuratowski.PairMember M x fx f ∧ Product projectionN i fx t

def Graph (S projection projectionN f g : M.Carrier .set) : Prop := ∀ s t,
  PureKuratowski.PairMember M s t g ↔ (Project.FirstOrderSemantics.reduct M).mem s S ∧
    Value projection projectionN f s t

def value {m : Nat} (projection projectionN f s t : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj
    (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ 2 1 s.succ.succ.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ 1 0))
      (ProjectSyntax.encode id (ForcingDiagramOrder.product projectionN.succ.succ.succ 2 0 t.succ.succ.succ))))))

theorem value_freeClosed {m : Nat} (projection projectionN f s t : Fin m) :
    (value projection projectionN f s t).FreeClosed := by
  simp -implicitDefEqProofs [value, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (projection projectionN f s t : Fin m) :
    Project.Formula.satisfies env (value projection projectionN f s t) ↔
      Value (env.bound projection) (env.bound projectionN) (env.bound f) (env.bound s) (env.bound t) := by
  simp only [value, Value, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

theorem value_unique {w D N mul mulN e node F G projection projectionN f s t u : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : MapsTo D N f) (hF : FactorTable w D mul node F)
    (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hEq : EqualityLaw w D mul F projection) (hEqN : EqualityLaw w N mulN G projectionN)
    (ht : Value projection projectionN f s t) (hu : Value projection projectionN f s u) : t = u := by
  obtain ⟨i,x,fx,hxs,hfx,hft⟩ := ht
  obtain ⟨j,y,fy,hys,hfy,hfu⟩ := hu
  exact (letter_eq_iff hEqN hft hfu).mpr
    (map_meets hm hf hF hPres hmap hfx hfy ((letter_eq_iff hEq hxs hys).mp rfl))

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N mul mulN e node F G C CN S SN projection projectionN f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : MapsTo D N f) (hF : FactorTable w D mul node F)
    (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hC : Representatives w D C) (hL : Letters w D mul F C S)
    (hProjection : Projection w D mul F C projection) (hEq : EqualityLaw w D mul F projection)
    (hCN : Representatives w N CN) (hpN : MapsTo CN SN projectionN)
    (hEqN : EqualityLaw w N mulN G projectionN) :
    ∃ g, MapsTo S SN g ∧ Graph S projection projectionN f g := by
  let schema : Project.BinarySchema 3 := {
    body := value 2 3 4 1 0
    freeClosed := value_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases projection (Fin.cases projectionN (fun _ => f)), free := fun _ => w }
  have he (s t) : schema.denote env s t ↔ Value projection projectionN f s t :=
    value_semantics hM ((env.push s).push t) 2 3 4 1 0
  obtain ⟨g,hg,hedge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := S) (target := SN) (by
      intro s hs
      obtain ⟨i,x,hi,hx,hxs⟩ := representative hC hL hProjection hs
      obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
      obtain ⟨t,_,hft⟩ := projected hM hCN hpN hi (hf.2 x fx hfx)
      exact ⟨t,(he s t).mpr ⟨i,x,fx,hxs,hfx,hft⟩⟩) (by
      intro s _ t u ht hu
      exact value_unique hm hf hF hPres hmap hEq hEqN ((he s t).mp ht) ((he s u).mp hu)) (by
      intro s t _ ht
      obtain ⟨i,x,fx,_,_,hft⟩ := (he s t).mp ht
      exact projected_range hpN hft)
  exact ⟨g,(ForcingSupportSize.native_mapsTo hM S SN g).mpr hg,
    fun s t => (hedge s t).trans (and_congr_right (fun _ => he s t))⟩

theorem map_letter (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N mul mulN e node F G C CN S SN projection projectionN f g i x fx s t : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : MapsTo D N f) (hF : FactorTable w D mul node F)
    (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hC : Representatives w D C) (hp : MapsTo C S projection) (hEq : EqualityLaw w D mul F projection)
    (hCN : Representatives w N CN) (hpN : MapsTo CN SN projectionN) (hEqN : EqualityLaw w N mulN G projectionN)
    (hg : Graph S projection projectionN f g) (hxs : Product projection i x s)
    (hfx : PureKuratowski.PairMember M x fx f) :
    PureKuratowski.PairMember M s t g ↔ Product projectionN i fx t := by
  constructor
  · intro hst
    obtain ⟨u,_,hfu⟩ := projected hM hCN hpN (projected_indices hC hp hxs).1 (hf.2 x fx hfx)
    have he := value_unique hm hf hF hPres hmap hEq hEqN ((hg s t).mp hst).2 ⟨i,x,fx,hxs,hfx,hfu⟩
    exact he.symm ▸ hfu
  · intro hft
    exact (hg s t).mpr ⟨projected_range hp hxs,i,x,fx,hxs,hfx,hft⟩

theorem graph_injective {w D N mul mulN e eN zero a fa node mapped F G S SN projection projectionN f g : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hp : Path w D mul e zero a node) (hpN : Path w N mulN eN zero fa mapped)
    (hF : FactorTable w D mul node F) (hG : FactorTable w N mulN mapped G)
    (hf : Injection D N f) (hPres : PreservesProducts mul mulN f) (hmap : FactorMap F G f)
    (hEq : EqualityLaw w D mul F projection) (hEqN : EqualityLaw w N mulN G projectionN)
    (hgm : MapsTo S SN g) (hg : Graph S projection projectionN f g) : Injection S SN g := by
  refine ⟨hgm,?_⟩
  intro s t z hs ht
  obtain ⟨i,x,fx,hxs,hfx,hfz⟩ := ((hg s z).mp hs).2
  obtain ⟨j,y,fy,hyt,hfy,hgz⟩ := ((hg t z).mp ht).2
  exact (letter_eq_iff hEq hxs hyt).mpr (reflect_meets hm hmN hp hpN hF hG hf hPres hmap hfx hfy
    ((letter_eq_iff hEqN hfz hgz).mp rfl))

end PPAC.Migration.ConstructionProbeLettersMap
