/- Pinned interpretedLetter_exit and the actual indexed presentation universal property. -/
import PPAC.Migration.ConstructionProbeInterpretedLettersSyntax

namespace PPAC.Migration.ConstructionProbePresentedLift
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeLiftHom ConstructionProbeInterpretedLetters
open ConstructionProbePresentationTransitions
open ConstructionProbeLetters (Representatives Letters Projection EqualityLaw)
open ConstructionProbeAction (ActionTable projected_indices)
open ConstructionProbePath (Path FactorTable)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeAlphabet (Alphabet ExitGraph)
open ConstructionProbeTarget (TargetGraph)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeGenerator (GeneratorGraph)
open ConstructionProbeIndexedGenerators (ProbeGraph presentedHom_ext)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Unit Associative)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Original hbexit: p(i)*f(b)=f(terminal(i)*d), using actual graph values. -/
def IndexedExit (terminal mul d b f p mulN : M.Carrier .set) : Prop := ∀ i t v pi fb fv,
  PureKuratowski.PairMember M i t terminal → Product mul t d v →
  PureKuratowski.PairMember M i pi p → PureKuratowski.PairMember M b fb f →
  PureKuratowski.PairMember M v fv f → Product mulN pi fb fv

/-- The pinned representative calculation, using source and target associativity. -/
theorem interpretation_exit (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node factor C S projection N J mulN f p Q terminal target d b E : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFactor : FactorTable w D mul node factor)
    (hC : Representatives w D C) (hProjection : MapsTo C S projection)
    (hEq : EqualityLaw w D mul factor projection) (hJ : Representatives N N J)
    (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j)
    (hQ : InterpretationGraph S f p mulN projection Q) (hT : MapsTo w D terminal)
    (hTarget : TargetGraph D mul projection terminal target) (hExit : ExitGraph mul target d E)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D)
    (hExitRel : IndexedExit terminal mul d b f p mulN) : ExitCompatible b E f Q mulN := by
  intro s z qs fb fz hsz hqs hfb hfz
  obtain ⟨u,hsu,hudz⟩ := (hExit s z).mp hsz
  obtain ⟨i,x,t,hx,hxs,hit,hxt⟩ := (hTarget s u).mp hsu
  have hi := (projected_indices hC hProjection hxs).1
  have ht := hT.2 i t hit
  obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
  obtain ⟨pi,hpi,_⟩ := hp.1.2 i hi
  obtain ⟨v,hv,htd⟩ := (hm.2.1 t ht).1 d hd
  obtain ⟨fv,hfv,_⟩ := hf.1.2 v hv
  have hqval := (interpretation_mk hM hm hFactor hProjection hEq hJ hMul hf hp hAssoc hPres hAll hQ hxs hfx hpi).mp hqs
  have hrel := hExitRel i t v pi fb fv hit htd hpi hfb hfv
  have hxv := (hm.2.2 x t d u v z hx ht hd hxt htd).mp hudz
  have hmap := hPres x v z fx fv fz hxv hfx hfv hfz
  exact (hAssoc fx pi fb qs fv fz (hf.2 x fx hfx) (hp.2 i pi hpi) (hf.2 b fb hfb) hqval hrel).mpr hmap

def PresentedLaws (zero D G mulN unit eN f p P L : M.Carrier .set) : Prop :=
  BasicLiftLaws zero D G mulN unit eN f L ∧
  (∀ i gen y, PureKuratowski.PairMember M i gen P →
    (PureKuratowski.PairMember M gen y L ↔ PureKuratowski.PairMember M i y p))

/-- Source presentedLift_old/probe. The old clause is inherited from liftHom. -/
theorem presented_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node factor C S projection N J mulN eN f p Q zero G unit K P L : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFactor : FactorTable w D mul node factor)
    (hProjection : MapsTo C S projection) (hEq : EqualityLaw w D mul factor projection)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hOne : PureKuratowski.PairMember M e eN f) (hUnit : Unit N mulN eN)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAll : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j)
    (hQ : InterpretationGraph S f p mulN projection Q) (hProbe : ProbeGraph w projection e K P)
    (hLift : LiftLaws zero D G mulN unit eN f Q K L) : PresentedLaws zero D G mulN unit eN f p P L := by
  refine ⟨hLift.1,?_⟩
  intro i gen y hgen
  obtain ⟨hi,s,his,hsg⟩ := (hProbe i gen).mp hgen
  constructor
  · intro hy
    obtain ⟨pi,hpi,_⟩ := hp.1.2 i hi
    have hsy := (hLift.2 s gen y hsg).mp hy
    have hprod := (interpretation_mk hM hm hFactor hProjection hEq hJ hMul hf hp hAssoc hPres hAll hQ his hOne hpi).mp hsy
    have he := ((hUnit.2 pi (hp.2 i pi hpi) y).1).mp hprod
    exact he.symm ▸ hpi
  · intro hy
    apply (hLift.2 s gen y hsg).mpr
    apply (interpretation_mk hM hm hFactor hProjection hEq hJ hMul hf hp hAssoc hPres hAll hQ his hOne hy).mpr
    exact ((hUnit.2 y (hp.2 i y hy) y).1).mpr rfl

/-- The source indexed universal property, with actual existence and graph uniqueness. -/
theorem existsUnique_presentedHom (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K C factor projection P N J mulN eN f p node a terminal target d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hC : Representatives w D C) (hLetters : Letters w D mul factor C S)
    (hProj : MapsTo C S projection) (hProjection : Projection w D mul factor C projection)
    (hEq : EqualityLaw w D mul factor projection) (hAction : ActionTable D mul projection A)
    (hPath : Path w D mul e zero a node) (hFactor : FactorTable w D mul node factor)
    (hP : MapsTo w W P) (hProbe : ProbeGraph w projection e K P)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hOne : PureKuratowski.PairMember M e eN f) (hUnitN : Unit N mulN eN)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAdj : Adjacent w factor f p mulN) (hT : MapsTo w D terminal)
    (hTarget : TargetGraph D mul projection terminal target) (hExit : ExitGraph mul target d E)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D)
    (hExitRel : IndexedExit terminal mul d b f p mulN) :
    ∃ L, MapsTo W N L ∧ PresentedLaws zero D G mulN unit eN f p P L ∧
      ∀ H, MapsTo W N H → PresentedLaws zero D G mulN unit eN f p P H → H = L := by
  have hAll := transitions_from_adjacent hM hw hm hPath hFactor hf hp hOne hUnitN hAssoc hPres hAdj
  obtain ⟨Q,hQ,hQGraph⟩ := exists_interpretation hM hm hFactor hC hLetters hProjection hEq hJ hMul hf hp hAssoc hPres hAll
  have hEquiv := interpretation_equivariant hM hm hFactor hC hProj hEq hAction hJ hMul hf hp hAssoc hPres hAll hQGraph
  have hExitQ := interpretation_exit hM hm hFactor hC hProj hEq hJ hMul hf hp hAssoc hPres hAll hQGraph hT hTarget hExit hd hExitRel
  obtain ⟨L,hL,hLGraph⟩ := ConstructionProbeHomEvaluationSyntax.exists_lift_graph hM hw hJ hMul hf hQ hW
  have hLift := lift_laws hM hw hz hzw hJ hMul hf hQ hUnitN hAssoc hPres hEquiv hExitQ
    hAlpha.2.2.2.1 hW hb hUnit hOne hG hK hGen hLGraph
  have hPresented := presented_laws hM hm hFactor hProj hEq hJ hMul hf hp hOne hUnitN hAssoc hPres hAll hQGraph hProbe hLift
  refine ⟨L,hL,hPresented,?_⟩
  intro H hH hPresentedH
  apply presentedHom_ext hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hC hLetters hProj hProjection
    hAction hP hProbe hMul hH hL hPresentedH.1.2.1 hPresented.1.2.1
  · intro x q hx y z hy hz'
    exact ForcingConditionGraphs.function_unique hf.1
      ((hPresentedH.1.2.2 x q y hx).mp hy) ((hPresented.1.2.2 x q z hx).mp hz')
  · intro i gen hgen y z hy hz'
    exact ForcingConditionGraphs.function_unique hp.1
      ((hPresentedH.2 i gen y hgen).mp hy) ((hPresented.2 i gen z hgen).mp hz')

/-- The original indexed exit and transition relations hold in the actual Word. -/
def ProbeRelations (zero D mul b d terminal factor P G : M.Carrier .set) : Prop :=
  (∀ i pi t z ob oz, PureKuratowski.PairMember M i pi P → PureKuratowski.PairMember M i t terminal →
    Product mul t d z → Old zero D b ob → Old zero D z oz → Product G pi ob oz) ∧
  (∀ i j r pi pj oldr, Product factor i j r → PureKuratowski.PairMember M i pi P →
    PureKuratowski.PairMember M j pj P → Old zero D r oldr → Product G oldr pj pi)

theorem probe_relations (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K C factor projection P node a terminal target d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hC : Representatives w D C) (hProj : MapsTo C S projection)
    (hEq : EqualityLaw w D mul factor projection) (hAction : ActionTable D mul projection A)
    (hPath : Path w D mul e zero a node) (hFactor : FactorTable w D mul node factor)
    (hProbe : ProbeGraph w projection e K P) (hT : MapsTo w D terminal)
    (hTarget : TargetGraph D mul projection terminal target) (hExit : ExitGraph mul target d E) :
    ProbeRelations zero D mul b d terminal factor P G := by
  constructor
  · intro i pi t z ob oz hpi hit htd hob hoz
    obtain ⟨_,letter,hletter,hgen⟩ := (hProbe i pi).mp hpi
    have htarget := (hTarget letter t).mpr ⟨i,e,t,hm.1.1,hletter,hit,
      ((hm.1.2 t (hT.2 i t hit) t).1).mpr rfl⟩
    exact ConstructionProbeGenerator.generator_mul_b hM hw hz hzw hm hAlpha hW hb hUnit hG
      ((hGen letter pi).mp hgen) (hK.2 letter pi hgen) ((hExit letter z).mpr ⟨t,htarget,htd⟩) hob hoz
  · intro i j r pi pj oldr hfactor hpi hpj hor
    obtain ⟨_,si,hsi,hgi⟩ := (hProbe i pi).mp hpi
    obtain ⟨_,sj,hsj,hgj⟩ := (hProbe j pj).mp hpj
    obtain ⟨_,hj,_,_⟩ := (hFactor i j r).mp hfactor
    obtain ⟨sk,_,hsk⟩ := ConstructionProbeAction.projected hM hC hProj hj hor.1
    have hself := (hFactor j j e).mpr ⟨hj,hj,Or.inl rfl,ConstructionProbePath.factor_self hm hPath.1 hj⟩
    have he : si = sk := (ConstructionProbeLetters.letter_eq_iff hEq hsi hsk).mpr
      ⟨j,r,hj,⟨hm.1.1,r,hfactor,((hm.1.2 r hor.1 r).1).mpr rfl⟩,
        ⟨hor.1,e,hself,((hm.1.2 r hor.1 r).2).mpr rfl⟩⟩
    subst sk
    have hact : Product A r sj si := (hAction r sj si).mpr
      ⟨hor.1,j,e,r,hm.1.1,hsj,((hm.1.2 r hor.1 r).2).mpr rfl,hsk⟩
    exact ConstructionProbeGenerator.old_mul_generator hM hw hz hzw hm hAlpha hW hb hG hor
      ((hGen sj pj).mp hgj) ((hGen si pi).mp hgi) (hK.2 sj pj hgj) hact

end PPAC.Migration.ConstructionProbePresentedLift
