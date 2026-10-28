/- Pinned LocalQuotients.localSetoid/LocalQuotient/ofName/ofName_eq.
Reuse the already adopted MergerCopies/LabelSet pattern: native Separation,
functional image and exact function graph. No representative choice or
host Quotient is used for the object collection. -/
import PPAC.Migration.ForcingLocalAtomic

namespace PPAC.Migration.ForcingLocalQuotient
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingMapConditions (MapRel)
open ForcingLocalAtomic (EqG eqG)
open ForcingSupportSize (MapsTo)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Class {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W g r X sigma cls : M.Carrier .set) : Prop :=
  ∀ tau, (Project.FirstOrderSemantics.reduct M).mem tau cls ↔
    (Project.FirstOrderSemantics.reduct M).mem tau X ∧ EqG R env W g r sigma tau

def eqClass {k m : Nat} (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W g r X sigma cls : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) cls.castSucc).iff
    ((Formula.mem (Fin.last m) X.castSucc).conj
      (eqG R (paramsUp rho) W.castSucc g.castSucc r.castSucc sigma.castSucc (Fin.last m))))

theorem eqClass_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (rho : Fin k → Fin m) (W g r X sigma cls : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (eqClass R rho W g r X sigma cls) ↔
      Class R (fun j => env (rho j)) (env W) (env g) (env r) (env X) (env sigma) (env cls) := by
  simp only [eqClass,Class,Source.Formula.iff,Formula.Realize,ForcingLocalAtomic.eqG_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (W g r X sigma : M.Carrier .set) :
    ∃ cls, Class R env W g r X sigma cls := by
  let params : Fin (k+4) → M.Carrier .set := Fin.addCases env (Fin.cases W (Fin.cases g (args2 r sigma)))
  let up : Fin k → Fin (k+4) := Fin.castAdd 4
  let wi : Fin (k+4) := Fin.natAdd k 0
  let gi : Fin (k+4) := Fin.natAdd k 1
  let ri : Fin (k+4) := Fin.natAdd k 2
  let si : Fin (k+4) := Fin.natAdd k 3
  let query := eqG R (paramsUp up) wi.castSucc gi.castSucc ri.castSucc si.castSucc (Fin.last (k+4))
  have hq : ∀ tau, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases tau params) query ↔ EqG R env W g r sigma tau := by
    intro tau
    simp only [query,ForcingLocalAtomic.eqG_semantics (M := M),params,up,wi,gi,ri,si,paramsUp,
      Fin.lastCases_last,Fin.lastCases_castSucc,Fin.addCases_left,Fin.addCases_right,Fin.cases_zero]
    rfl
  have sep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨cls,hcls⟩ := sep params X
  exact ⟨cls,fun tau => (hcls tau).trans (and_congr Iff.rfl (hq tau))⟩

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {W g r X sigma c d : M.Carrier .set}
    (hc : Class R env W g r X sigma c) (hd : Class R env W g r X sigma d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun tau => (hc tau).trans (hd tau).symm)

def Classes {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W g r X Q : M.Carrier .set) : Prop :=
  ∀ cls, (Project.FirstOrderSemantics.reduct M).mem cls Q ↔
    ∃ sigma, (Project.FirstOrderSemantics.reduct M).mem sigma X ∧ Class R env W g r X sigma cls

def classes {k m : Nat} (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W g r X Q : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) Q.castSucc).iff
    (.ex ((Formula.mem (Fin.last (m+1)) X.castSucc.castSucc).conj
      (eqClass R (paramsUp (paramsUp rho)) W.castSucc.castSucc g.castSucc.castSucc r.castSucc.castSucc
        X.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem classes_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (rho : Fin k → Fin m) (W g r X Q : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (classes R rho W g r X Q) ↔
      Classes R (fun j => env (rho j)) (env W) (env g) (env r) (env X) (env Q) := by
  simp only [classes,Classes,Source.Formula.iff,Formula.Realize,eqClass_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

def Projection {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W g r X f : M.Carrier .set) : Prop :=
  ∀ sigma cls, PureKuratowski.PairMember M sigma cls f ↔
    (Project.FirstOrderSemantics.reduct M).mem sigma X ∧ Class R env W g r X sigma cls

def projection {k m : Nat} (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W g r X f : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc X.castSucc.castSucc).conj
      (eqClass R (paramsUp (paramsUp rho)) W.castSucc.castSucc g.castSucc.castSucc r.castSucc.castSucc
        X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem projection_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (rho : Fin k → Fin m) (W g r X f : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (projection R rho W g r X f) ↔
      Projection R (fun j => env (rho j)) (env W) (env g) (env r) (env X) (env f) := by
  simp only [projection,Projection,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    eqClass_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x y => ⟨(h x y).1,(h x y).2⟩,fun h x y => ⟨(h x y).mp,(h x y).mpr⟩⟩

/-- The native functional image is the exact quotient carrier; the existing
native function constructor retains the exact representative-to-class graph. -/
theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (W g r X : M.Carrier .set) :
    ∃ Q f, MapsTo X Q f ∧ Classes R env W g r X Q ∧ Projection R env W g r X f := by
  let params : Fin (k+4) → M.Carrier .set := Fin.addCases env (Fin.cases W (Fin.cases g (args2 r X)))
  let up : Fin k → Fin (k+4) := Fin.castAdd 4
  let wi : Fin (k+4) := Fin.natAdd k 0
  let gi : Fin (k+4) := Fin.natAdd k 1
  let ri : Fin (k+4) := Fin.natAdd k 2
  let xi : Fin (k+4) := Fin.natAdd k 3
  let query := eqClass R (paramsUp (paramsUp up)) wi.castSucc.castSucc gi.castSucc.castSucc
    ri.castSucc.castSucc xi.castSucc.castSucc (Fin.last (k+4)).castSucc (Fin.last (k+4+1))
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) (k+4) :=
    { bound := fun i => params i.rev, free := fun _ => X }
  have hRel : ∀ sigma cls, (ProjectSyntax.binary query).denote penv sigma cls ↔ Class R env W g r X sigma cls := by
    intro sigma cls
    rw [ForcingMapConditions.binary_semantics hM query params X sigma cls]
    simp only [MapRel,query,eqClass_semantics (M := M),params,up,wi,gi,ri,xi,paramsUp,
      Fin.lastCases_last,Fin.lastCases_castSucc,Fin.addCases_left,Fin.addCases_right,
      Fin.cases_zero]
    rfl
  have ht : ∀ sigma, (Project.FirstOrderSemantics.reduct M).mem sigma X →
      ∃ cls, (ProjectSyntax.binary query).denote penv sigma cls := by
    intro sigma _
    obtain ⟨cls,hcls⟩ := exists_class hM R env W g r X sigma
    exact ⟨cls,(hRel sigma cls).mpr hcls⟩
  have hu : ∀ sigma c d, (ProjectSyntax.binary query).denote penv sigma c →
      (ProjectSyntax.binary query).denote penv sigma d → c = d := by
    intro sigma c d hc hd
    exact class_unique hM ((hRel sigma c).mp hc) ((hRel sigma d).mp hd)
  obtain ⟨Q,hQ⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary query) penv X ht hu
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) penv (source := X) (target := Q)
    ht (fun sigma _ c d hc hd => hu sigma c d hc hd)
    (fun sigma cls hs hc => (hQ cls).mpr ⟨sigma,hs,hc⟩)
  refine ⟨Q,f,(ForcingSupportSize.native_mapsTo hM X Q f).mpr hf,?_,?_⟩
  · intro cls
    exact (hQ cls).trans ⟨fun ⟨sigma,hs,hc⟩ => ⟨sigma,hs,(hRel sigma cls).mp hc⟩,
      fun ⟨sigma,hs,hc⟩ => ⟨sigma,hs,(hRel sigma cls).mpr hc⟩⟩
  · exact fun sigma cls => (he sigma cls).trans (and_congr Iff.rfl (hRel sigma cls))

theorem projection_onto {k : Nat} {R : Formula (k+2)} {env : Fin k → M.Carrier .set}
    {W g r X Q f cls : M.Carrier .set}
    (hQ : Classes R env W g r X Q) (hf : Projection R env W g r X f)
    (hc : (Project.FirstOrderSemantics.reduct M).mem cls Q) :
    ∃ sigma, (Project.FirstOrderSemantics.reduct M).mem sigma X ∧ PureKuratowski.PairMember M sigma cls f := by
  obtain ⟨sigma,hs,hcls⟩ := (hQ cls).mp hc
  exact ⟨sigma,hs,(hf sigma cls).mpr ⟨hs,hcls⟩⟩

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r X sigma tau c d : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (ht : (Project.FirstOrderSemantics.reduct M).mem tau X)
    (hc : Class (orderFormula (rho 0) mul) env (env (rho 6)) g r X sigma c)
    (hd : Class (orderFormula (rho 0) mul) env (env (rho 6)) g r X tau d) :
    c = d ↔ EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau := by
  constructor
  · intro he
    have hself := (hd tau).mpr ⟨ht,ForcingLocalAtomic.eqG_refl hM env rho mul hm hp hg hr tau⟩
    exact ((hc tau).mp (he.symm ▸ hself)).2
  · intro he
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro upsilon
    rw [hc upsilon,hd upsilon]
    exact and_congr_right fun _ => ⟨
      fun h => ForcingLocalAtomic.eqG_trans hM env rho mul hm hp hg hr (ForcingLocalAtomic.eqG_symm hM he) h,
      fun h => ForcingLocalAtomic.eqG_trans hM env rho mul hm hp hg hr he h⟩

def EqualityLaw {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W g r f : M.Carrier .set) : Prop :=
  ∀ sigma tau c d, PureKuratowski.PairMember M sigma c f → PureKuratowski.PairMember M tau d f →
    (c = d ↔ EqG R env W g r sigma tau)

def equalityLaw {k m : Nat} (R : Formula (k+2)) (rho : Fin k → Fin m)
    (W g r f : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let sigma := (Fin.last m).castSucc.castSucc.castSucc
  let tau := (Fin.last (m+1)).castSucc.castSucc
  let c := (Fin.last (m+2)).castSucc
  let d := Fin.last (m+3)
  .all (.all (.all (.all ((Source.SetLanguage.edge (up f) sigma c).imp
    ((Source.SetLanguage.edge (up f) tau d).imp
      ((Formula.equal c d).iff (eqG R (fun j => up (rho j)) (up W) (up g) (up r) sigma tau)))))))

theorem equalityLaw_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (rho : Fin k → Fin m) (W g r f : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (equalityLaw R rho W g r f) ↔
      EqualityLaw R (fun j => env (rho j)) (env W) (env g) (env r) (env f) := by
  simp only [equalityLaw,EqualityLaw,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    ForcingLocalAtomic.eqG_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h s t c d hc hd => ⟨(h s t c d hc hd).1,(h s t c d hc hd).2⟩,
    fun h s t c d hc hd => ⟨(h s t c d hc hd).mp,(h s t c d hc hd).mpr⟩⟩

theorem equality_law (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r X f : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r)
    (hf : Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X f) :
    EqualityLaw (orderFormula (rho 0) mul) env (env (rho 6)) g r f := by
  intro sigma tau c d hc hd
  obtain ⟨_,hc⟩ := (hf sigma c).mp hc
  obtain ⟨ht,hd⟩ := (hf tau d).mp hd
  exact class_eq_iff hM env rho mul hm hp hg hr ht hc hd


/-- Construct the actual LocalName carrier, all its EqG classes and the exact
surjective projection. Equivalence is proved from the concrete atomic laws. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e g r G F nameBound H : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : ForcingSupportSize.Injection (env (rho 0)) I r) :
    ∃ X Q f, ForcingLocalNames.Carrier (fun j => env (rho j)) G F nameBound H X ∧
      MapsTo X Q f ∧ Classes (orderFormula (rho 0) mul) env (env (rho 6)) g r X Q ∧
      Projection (orderFormula (rho 0) mul) env (env (rho 6)) g r X f ∧
      EqualityLaw (orderFormula (rho 0) mul) env (env (rho 6)) g r f := by
  obtain ⟨X,hX⟩ := ForcingLocalNames.exists_carrier hM (fun j => env (rho j)) G F nameBound H
  obtain ⟨Q,f,hf,hQ,hProjection⟩ := exists_quotient hM (orderFormula (rho 0) mul) env (env (rho 6)) g r X
  exact ⟨X,Q,f,hX,hf,hQ,hProjection,equality_law hM env rho mul hm hp hg hr hProjection⟩

def result {k : Nat} (rho : Fin 7 → Fin k) (mul g r G F nameBound H : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let X := (Fin.last k).castSucc.castSucc
  let Q := (Fin.last (k+1)).castSucc
  let f := Fin.last (k+2)
  .ex (.ex (.ex ((ForcingLocalNames.carrier (fun j => up (rho j)) (up G) (up F) (up nameBound) (up H) X).conj
    ((Source.SetLanguage.mapsTo f X Q).conj
      ((classes R up (up (rho 6)) (up g) (up r) X Q).conj
        ((projection R up (up (rho 6)) (up g) (up r) X f).conj
          (equalityLaw R up (up (rho 6)) (up g) (up r) f)))))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (mul g r G F nameBound H : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result rho mul g r G F nameBound H) ↔
    ∃ X Q f, ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env nameBound) (env H) X ∧
      MapsTo X Q f ∧ Classes (orderFormula (rho 0) mul) env (env (rho 6)) (env g) (env r) X Q ∧
      Projection (orderFormula (rho 0) mul) env (env (rho 6)) (env g) (env r) X f ∧
      EqualityLaw (orderFormula (rho 0) mul) env (env (rho 6)) (env g) (env r) f := by
  simp only [result,Formula.Realize,ForcingLocalNames.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),classes_semantics (M := M),
    projection_semantics (M := M),equalityLaw_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r G F nameBound J H : Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp
    ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
      ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp
        ((Source.SetLanguage.injection r (rho 0) I).imp
          ((ForcingSupportedNames.range (rho 0) r J).imp
            ((ForcingLabelPermutations.fixing G J H).imp
              (result rho mul g r G F nameBound H))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r G F nameBound J H : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w e mul g r G F nameBound J H)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hg hr _hRange _hFix
  apply (result_semantics (M := M) env rho mul g r G F nameBound H).mpr
  exact construct hM env rho mul
    ((ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm)
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg)
    ((ForcingSupportSize.injection_semantics (M := M) env r (rho 0) I).mp hr)

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r G F nameBound J H : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (constructionSentence rho I K B w e mul g r G F nameBound J H)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w e mul g r G F nameBound J H hM)

end PPAC.Migration.ForcingLocalQuotient
