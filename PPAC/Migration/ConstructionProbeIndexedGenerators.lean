/- Pinned Path.probe and the generator factorization in Path.presentedHom_ext.
All indices belong to the internal omega; reuse the actual letter projection. -/
import PPAC.Migration.ConstructionProbeHomExtSyntax

namespace PPAC.Migration.ConstructionProbeIndexedGenerators
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeLiftHom ConstructionProbeHomExt
open ConstructionProbeLetters (Representatives Letters Projection)
open ConstructionProbeAction (ActionTable projected representative)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeGenerator (GeneratorGraph)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Probe (projection e K i q : M.Carrier .set) : Prop :=
  ∃ s, Product projection i e s ∧ PureKuratowski.PairMember M s q K

def probe {m : Nat} (projection e K i q : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ i.succ e.succ 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ 0 q.succ)))

theorem probe_freeClosed {m : Nat} (projection e K i q : Fin m) : (probe projection e K i q).FreeClosed := by
  simp -implicitDefEqProofs [probe,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem probe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (projection e K i q : Fin m) :
    Project.Formula.satisfies env (probe projection e K i q) ↔
      Probe (env.bound projection) (env.bound e) (env.bound K) (env.bound i) (env.bound q) := by
  simp only [probe,Probe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def ProbeGraph (w projection e K P : M.Carrier .set) : Prop := ∀ i q,
  PureKuratowski.PairMember M i q P ↔
    (Project.FirstOrderSemantics.reduct M).mem i w ∧ Probe projection e K i q

theorem exists_probe_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D C S projection e K W : M.Carrier .set}
    (hC : Representatives w D C) (hp : MapsTo C S projection)
    (heD : (Project.FirstOrderSemantics.reduct M).mem e D) (hK : MapsTo S W K) :
    ∃ P, MapsTo w W P ∧ ProbeGraph w projection e K P := by
  let schema : Project.BinarySchema 3 := {
    body := probe 2 3 4 1 0
    freeClosed := probe_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases projection (Fin.cases e (fun _ => K)), free := fun _ => w }
  have he (i q : M.Carrier .set) : schema.denote env i q ↔ Probe projection e K i q :=
    probe_semantics hM ((env.push i).push q) 2 3 4 1 0
  obtain ⟨P,hP,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := w) (target := W) (by
      intro i hi
      obtain ⟨s,hs,his⟩ := projected hM hC hp hi heD
      obtain ⟨q,hq,_⟩ := hK.1.2 s hs
      exact ⟨q,(he i q).mpr ⟨s,his,hq⟩⟩) (by
      intro i _ q r hq hr
      obtain ⟨s,his,hq⟩ := (he i q).mp hq
      obtain ⟨t,hit,hr⟩ := (he i r).mp hr
      have hst := ConstructionProbeHomEvaluation.product_unique hM hp his hit
      subst t
      exact ForcingConditionGraphs.function_unique hK.1 hq hr) (by
      intro i q _ hq
      obtain ⟨s,_,hq⟩ := (he i q).mp hq
      exact hK.2 s q hq)
  exact ⟨P,(ForcingSupportSize.native_mapsTo hM w W P).mpr hP,
    fun i q => (hgraph i q).trans (and_congr_right (fun _ => he i q))⟩

/-- The exact source factorization generator(letter i x) = old(x) * probe(i). -/
theorem generator_factor (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K C T projection P s gen : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hC : Representatives w D C) (hLetters : Letters w D mul T C S)
    (hp : MapsTo C S projection) (hProjection : Projection w D mul T C projection)
    (hAction : ActionTable D mul projection A) (hProbe : ProbeGraph w projection e K P)
    (hgen : PureKuratowski.PairMember M s gen K) :
    ∃ i x ox pi, (Project.FirstOrderSemantics.reduct M).mem i w ∧ Old zero D x ox ∧
      PureKuratowski.PairMember M i pi P ∧ Product G ox pi gen := by
  have hs := ForcingConditionGraphs.function_input hK.1 hgen
  obtain ⟨i,x,hi,hx,hxs⟩ := representative hC hLetters hProjection hs
  obtain ⟨t,ht,het⟩ := projected hM hC hp hi hm.1.1
  obtain ⟨pi,hpi,_⟩ := hK.1.2 t ht
  obtain ⟨ox,hox⟩ := exists_old hM hx (zero := zero)
  have hact : Product A x t s := (hAction x t s).mpr
    ⟨hx,i,e,x,hm.1.1,het,((hm.1.2 x hx x).2).mpr rfl,hxs⟩
  exact ⟨i,x,ox,pi,hi,hox,(hProbe i pi).mpr ⟨hi,t,het,hpi⟩,
    ConstructionProbeGenerator.old_mul_generator hM hw hz hzw hm hAlpha hW hb hG hox
      ((hGen t pi).mp hpi) ((hGen s gen).mp hgen) (hK.2 t pi hpi) hact⟩

/-- Pinned Path.presentedHom_ext: agreement only on the indexed probes suffices. -/
theorem presentedHom_ext (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K C T projection P N J mulN F H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hC : Representatives w D C) (hLetters : Letters w D mul T C S)
    (hp : MapsTo C S projection) (hProjection : Projection w D mul T C projection)
    (hAction : ActionTable D mul projection A) (hP : MapsTo w W P) (hProbe : ProbeGraph w projection e K P)
    (hMul : MapsTo J N mulN) (hF : MapsTo W N F) (hH : MapsTo W N H)
    (hFP : PreservesProducts G mulN F) (hHP : PreservesProducts G mulN H)
    (hOld : ∀ x q, Old zero D x q → AgreeAt q F H)
    (hNew : ∀ i q, PureKuratowski.PairMember M i q P → AgreeAt q F H) : F = H := by
  apply hom_ext hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hMul hF hH hFP hHP hOld
  intro s gen hgen y z hy hz'
  obtain ⟨i,x,ox,pi,_,hox,hpi,hprod⟩ := generator_factor hM hw hz hzw hm hAlpha hW hb hG
    hK hGen hC hLetters hp hProjection hAction hProbe hgen
  have hoxW := ConstructionProbeOldEmbedding.old_word hM hz hzw hW hox
  have hpiW := hP.2 i pi hpi
  obtain ⟨fx,hfx,_⟩ := hF.1.2 ox hoxW
  obtain ⟨hx,hhx,_⟩ := hH.1.2 ox hoxW
  obtain ⟨fp,hfp,_⟩ := hF.1.2 pi hpiW
  obtain ⟨hp',hhp,_⟩ := hH.1.2 pi hpiW
  have hex := hOld x ox hox fx hx hfx hhx
  have hep := hNew i pi hpi fp hp' hfp hhp
  subst hx
  subst hp'
  exact ConstructionProbeHomEvaluation.product_unique hM hMul
    (hFP ox pi gen fx fp y hprod hfx hfp hy) (hHP ox pi gen fx fp z hprod hhx hhp hz')

end PPAC.Migration.ConstructionProbeIndexedGenerators
