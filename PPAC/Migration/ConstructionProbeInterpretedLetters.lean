/- Pinned Path.interpretedLetter: descend f(x)*p(i) through the actual letter quotient. -/
import PPAC.Migration.ConstructionProbePresentationTransitionsSyntax

namespace PPAC.Migration.ConstructionProbeInterpretedLetters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePresentationTransitions
open ConstructionProbeLetters (Representatives Letters Projection EqualityLaw letter_eq_iff)
open ConstructionProbeAction (projected representative projected_indices projected_range ActionTable)
open ConstructionProbePath (FactorTable)
open ConstructionProbeTransitions (Transition product_closed)
open ConstructionProbeLiftHom (PreservesProducts Equivariant)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Associative)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (f p mulN projection s y : M.Carrier .set) : Prop := ∃ i x fx pi,
  Product projection i x s ∧ PureKuratowski.PairMember M x fx f ∧
  PureKuratowski.PairMember M i pi p ∧ Product mulN fx pi y

def value {m : Nat} (f p mulN projection s y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
    projection.succ.succ.succ.succ 3 2 s.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ.succ.succ 2 1)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge p.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    mulN.succ.succ.succ.succ 1 0 y.succ.succ.succ.succ)))))))))

theorem value_freeClosed {m : Nat} (f p mulN projection s y : Fin m) : (value f p mulN projection s y).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f p mulN projection s y : Fin m) :
    Project.Formula.satisfies env (value f p mulN projection s y) ↔
      Value (env.bound f) (env.bound p) (env.bound mulN) (env.bound projection) (env.bound s) (env.bound y) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

/-- The original lift compatibility calculation, with actual graph values. -/
theorem value_transition {w D mul node factor N mulN f p i j x z fx fz pi pj y : M.Carrier .set}
    (hFactor : FactorTable w D mul node factor) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j)
    (ht : Transition D mul factor i j x z)
    (hfx : PureKuratowski.PairMember M x fx f) (hfz : PureKuratowski.PairMember M z fz f)
    (hpi : PureKuratowski.PairMember M i pi p) (hpj : PureKuratowski.PairMember M j pj p)
    (hy : Product mulN fx pi y) : Product mulN fz pj y := by
  obtain ⟨_,d,hd,hxd⟩ := ht
  obtain ⟨hi,hj,hij,hd'⟩ := (hFactor i j d).mp hd
  obtain ⟨fd,hfd,_⟩ := hf.1.2 d hd'.choose_spec.choose_spec.2.2.1
  have htrans := hAll j hj i hi hij d fd pi pj hd hfd hpi hpj
  have hmul := hPres x d z fx fd fz hxd hfx hfd hfz
  exact (hAssoc fx fd pj fz pi y (hf.2 x fx hfx) (hf.2 d fd hfd) (hp.2 j pj hpj) hmul htrans).mpr hy

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul factor C S projection N J mulN f p s : M.Carrier .set}
    (hC : Representatives w D C) (hS : Letters w D mul factor C S)
    (hProjection : Projection w D mul factor C projection) (hJ : Representatives N N J)
    (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) : ∃ y, Value f p mulN projection s y := by
  obtain ⟨i,x,hi,hx,hxs⟩ := representative hC hS hProjection hs
  obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
  obtain ⟨pi,hpi,_⟩ := hp.1.2 i hi
  obtain ⟨y,_,hy⟩ := projected hM hJ hMul (hf.2 x fx hfx) (hp.2 i pi hpi)
  exact ⟨y,i,x,fx,pi,hxs,hfx,hpi,hy⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node factor projection N J mulN f p s y z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFactor : FactorTable w D mul node factor)
    (hEq : EqualityLaw w D mul factor projection) (hMul : MapsTo J N mulN)
    (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j)
    (hy : Value f p mulN projection s y) (hz : Value f p mulN projection s z) : y = z := by
  obtain ⟨i,x,fx,pi,hxs,hfx,hpi,hy⟩ := hy
  obtain ⟨j,v,fv,pj,hvs,hfv,hpj,hz⟩ := hz
  obtain ⟨k,t,hk,hxt,hvt⟩ := (letter_eq_iff hEq hxs hvs).mp rfl
  obtain ⟨ft,hft,_⟩ := hf.1.2 t (ConstructionProbeTransitions.transition_closed hm hFactor hxt)
  obtain ⟨pk,hpk,_⟩ := hp.1.2 k hk
  exact ConstructionProbeHomEvaluation.product_unique hM hMul
    (value_transition hFactor hf hp hAssoc hPres hAll hxt hfx hft hpi hpk hy)
    (value_transition hFactor hf hp hAssoc hPres hAll hvt hfv hft hpj hpk hz)

def InterpretationGraph (S f p mulN projection Q : M.Carrier .set) : Prop := ∀ s y,
  PureKuratowski.PairMember M s y Q ↔
    (Project.FirstOrderSemantics.reduct M).mem s S ∧ Value f p mulN projection s y

theorem exists_interpretation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node factor C S projection N J mulN f p : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFactor : FactorTable w D mul node factor)
    (hC : Representatives w D C) (hS : Letters w D mul factor C S)
    (hProjection : Projection w D mul factor C projection) (hEq : EqualityLaw w D mul factor projection)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j) :
    ∃ Q, MapsTo S N Q ∧ InterpretationGraph S f p mulN projection Q := by
  let schema : Project.BinarySchema 4 := {
    body := value 2 3 4 5 1 0
    freeClosed := value_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases f (Fin.cases p (Fin.cases mulN (fun _ => projection))), free := fun _ => w }
  have he (s y : M.Carrier .set) : schema.denote env s y ↔ Value f p mulN projection s y :=
    value_semantics hM ((env.push s).push y) 2 3 4 5 1 0
  obtain ⟨Q,hQ,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := S) (target := N) (by
      intro s hs
      obtain ⟨y,hy⟩ := value_total hM hC hS hProjection hJ hMul hf hp hs
      exact ⟨y,(he s y).mpr hy⟩) (by
      intro s _ y z hy hz
      exact value_unique hM hm hFactor hEq hMul hf hp hAssoc hPres hAll ((he s y).mp hy) ((he s z).mp hz)) (by
      intro s y _ hy
      obtain ⟨_,_,_,_,_,_,_,hy⟩ := (he s y).mp hy
      exact projected_range hMul hy)
  exact ⟨Q,(ForcingSupportSize.native_mapsTo hM S N Q).mpr hQ,
    fun s y => (hgraph s y).trans (and_congr_right (fun _ => he s y))⟩

/-- Source interpretedLetter_mk for every actual representative. -/
theorem interpretation_mk (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node factor C S projection N J mulN f p Q i x s fx pi y : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFactor : FactorTable w D mul node factor)
    (hProjection : MapsTo C S projection)
    (hEq : EqualityLaw w D mul factor projection) (hJ : Representatives N N J)
    (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j)
    (hQ : InterpretationGraph S f p mulN projection Q)
    (hxs : Product projection i x s) (hfx : PureKuratowski.PairMember M x fx f)
    (hpi : PureKuratowski.PairMember M i pi p) :
    PureKuratowski.PairMember M s y Q ↔ Product mulN fx pi y := by
  constructor
  · intro hy
    obtain ⟨z,_,hz⟩ := projected hM hJ hMul (hf.2 x fx hfx) (hp.2 i pi hpi)
    have he := value_unique hM hm hFactor hEq hMul hf hp hAssoc hPres hAll
      ((hQ s y).mp hy).2 ⟨i,x,fx,pi,hxs,hfx,hpi,hz⟩
    exact he.symm ▸ hz
  · intro hy
    exact (hQ s y).mpr ⟨projected_range hProjection hxs,i,x,fx,pi,hxs,hfx,hpi,hy⟩

/-- Pinned interpretedLetter_act, by the existing representative action equation. -/
theorem interpretation_equivariant (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node factor C S projection A N J mulN f p Q : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFactor : FactorTable w D mul node factor)
    (hC : Representatives w D C) (hProjection : MapsTo C S projection)
    (hEq : EqualityLaw w D mul factor projection) (hAction : ActionTable D mul projection A)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j)
    (hQ : InterpretationGraph S f p mulN projection Q) : Equivariant A f Q mulN := by
  intro b s t fb qs qt hact hfb hqs hqt
  obtain ⟨hb,i,x,bx,hx,hxs,hbx,hbxt⟩ := (hAction b s t).mp hact
  obtain ⟨hi,_⟩ := projected_indices hC hProjection hxs
  obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
  obtain ⟨fbx,hfbx,_⟩ := hf.1.2 bx (product_closed hm hb hx hbx)
  obtain ⟨pi,hpi,_⟩ := hp.1.2 i hi
  have hs := (interpretation_mk hM hm hFactor hProjection hEq hJ hMul hf hp hAssoc hPres hAll hQ hxs hfx hpi).mp hqs
  have ht := (interpretation_mk hM hm hFactor hProjection hEq hJ hMul hf hp hAssoc hPres hAll hQ hbxt hfbx hpi).mp hqt
  have hmul := hPres b x bx fb fx fbx hbx hfb hfx hfbx
  exact (hAssoc fb fx pi fbx qs qt (hf.2 b fb hfb) (hf.2 x fx hfx) (hp.2 i pi hpi) hmul hs).mp ht

end PPAC.Migration.ConstructionProbeInterpretedLetters
