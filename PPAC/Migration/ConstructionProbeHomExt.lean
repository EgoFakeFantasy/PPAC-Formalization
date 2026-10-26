/- Pinned ProbeWords.Word.hom_ext (688-700), consumed by Path.presentedHom_ext.
Use the existing formula-indexed Raw induction and actual generator product. -/
import PPAC.Migration.ConstructionProbeLiftHomSyntax

namespace PPAC.Migration.ConstructionProbeHomExt
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeLiftHom
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeGenerator (GeneratorGraph)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def AgreeAt (q F H : M.Carrier .set) : Prop := ∀ y z,
  PureKuratowski.PairMember M q y F → PureKuratowski.PairMember M q z H → y = z

def agreeAt {m : Nat} (q F H : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ q.succ.succ 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ q.succ.succ 0))
      (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))

theorem agreeAt_freeClosed {m : Nat} (q F H : Fin m) : (agreeAt q F H).FreeClosed := by
  simp -implicitDefEqProofs [agreeAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem agreeAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (q F H : Fin m) :
    Project.Formula.satisfies env (agreeAt q F H) ↔ AgreeAt (env.bound q) (env.bound F) (env.bound H) := by
  simp only [agreeAt,AgreeAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

def agreement {m : Nat} (W F H q : Fin m) : Project.Formula 1 m :=
  .imp (.mem (.bound q) (.bound W)) (agreeAt q F H)

theorem agreement_freeClosed {m : Nat} (W F H q : Fin m) : (agreement W F H q).FreeClosed := by
  simp -implicitDefEqProofs [agreement,Definitional.Formula.FreeClosed,agreeAt_freeClosed]

theorem agreement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W F H q : Fin m) :
    Project.Formula.satisfies env (agreement W F H q) ↔
      ((Project.FirstOrderSemantics.reduct M).mem (env.bound q) (env.bound W) →
        AgreeAt (env.bound q) (env.bound F) (env.bound H)) := by
  simp only [agreement,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,agreeAt_semantics hM]

/-- Source normal-form induction: old agreement and generator agreement determine every word. -/
theorem pointwise (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K N J mulN F H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hMul : MapsTo J N mulN) (hF : MapsTo W N F) (hH : MapsTo W N H)
    (hFP : PreservesProducts G mulN F) (hHP : PreservesProducts G mulN H)
    (hOld : ∀ x q, Old zero D x q → AgreeAt q F H)
    (hNew : ∀ s q, PureKuratowski.PairMember M s q K → AgreeAt q F H) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → AgreeAt q F H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases W (Fin.cases F (fun _ => H))
    free := fun _ => w }
  let p : Project.UnarySchema 3 := {
    body := agreement 1 2 3 0
    freeClosed := agreement_freeClosed _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ((Project.FirstOrderSemantics.reduct M).mem q W → AgreeAt q F H) :=
    agreement_semantics hM (env.push q) 1 2 3 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hx
    exact (he q).mpr (fun _ => hOld x q hx)) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro hq y z hy hz'
    obtain ⟨ht,hnot⟩ := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp ((hW q).mp hq)
    have htW := (hW t).mpr ht
    obtain ⟨gen,hgen,_⟩ := hK.1.2 s (cons_letter hCons)
    have hgW := hK.2 s gen hgen
    have hp := ConstructionProbeGenerator.generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb
      hUnit hG ((hGen s gen).mp hgen) hgW htW hnot hCons
    obtain ⟨fg,hfg,_⟩ := hF.1.2 gen hgW
    obtain ⟨hg,hhg,_⟩ := hH.1.2 gen hgW
    obtain ⟨ft,hft,_⟩ := hF.1.2 t htW
    obtain ⟨ht',hht,_⟩ := hH.1.2 t htW
    have heg := hNew s gen hgen fg hg hfg hhg
    have het := (he t).mp ih htW ft ht' hft hht
    subst hg
    subst ht'
    exact ConstructionProbeHomEvaluation.product_unique hM hMul
      (hFP gen t q fg ft y hp hfg hft hy) (hHP gen t q fg ft z hp hhg hht hz'))
  intro q hq
  exact (he q).mp (hAll q (word_raw hW hq)) hq

/-- Equality of the actual internal function graphs, not just their host interpretations. -/
theorem hom_ext (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K N J mulN F H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hMul : MapsTo J N mulN) (hF : MapsTo W N F) (hH : MapsTo W N H)
    (hFP : PreservesProducts G mulN F) (hHP : PreservesProducts G mulN H)
    (hOld : ∀ x q, Old zero D x q → AgreeAt q F H)
    (hNew : ∀ s q, PureKuratowski.PairMember M s q K → AgreeAt q F H) : F = H := by
  have he := pointwise hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hMul hF hH hFP hHP hOld hNew
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM W N F).mp hF).1.1
    ((ForcingSupportSize.native_mapsTo hM W N H).mp hH).1.1
  intro q y
  constructor
  · intro hy
    have hq := ForcingConditionGraphs.function_input hF.1 hy
    obtain ⟨z,hz',_⟩ := hH.1.2 q hq
    exact (he q hq y z hy hz').symm ▸ hz'
  · intro hy
    have hq := ForcingConditionGraphs.function_input hH.1 hy
    obtain ⟨z,hz',_⟩ := hF.1.2 q hq
    exact (he q hq z y hz' hy) ▸ hz'

/-- Uniqueness for two lifts with the same old and generator values. -/
theorem lift_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K N J mulN eN F Q L H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K)
    (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hL : MapsTo W N L) (hH : MapsTo W N H)
    (hLL : LiftLaws zero D G mulN unit eN F Q K L)
    (hHL : LiftLaws zero D G mulN unit eN F Q K H) : L = H := by
  apply hom_ext hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hMul hL hH hLL.1.2.1 hHL.1.2.1
  · intro x q hx y z hy hz'
    exact ForcingConditionGraphs.function_unique hF.1
      ((hLL.1.2.2 x q y hx).mp hy) ((hHL.1.2.2 x q z hx).mp hz')
  · intro s gen hgen y z hy hz'
    exact ForcingConditionGraphs.function_unique hQ.1
      ((hLL.2 s gen y hgen).mp hy) ((hHL.2 s gen z hgen).mp hz')

end PPAC.Migration.ConstructionProbeHomExt
