/- Pinned ProbeWords.Path.old_cone_intersection/common_multiple_reflection
and ConservativeExtensions.Path.oldHom_conservative. Reuse the existing full
letter-cone laws and actual old embedding; only the source old/cons cases remain. -/
import PPAC.Migration.ConstructionProbeOldEmbeddingSyntax
import PPAC.Migration.ConstructionProbeAlphabetMapSyntax

namespace PPAC.Migration.ConstructionProbeConservative
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Old cases_raw)
open ConstructionProbeRawAction (HeadDiv headDiv_old_iff headDiv_cons_iff cons_letter)
open ConstructionProbeOldEmbedding (OldGraph exists_old_graph)
open ConstructionProbeOldEmbeddingSyntax (EmbeddingLaws embedding_laws)
open ConstructionProbeCones (ConeLaws JoinProperty)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeAlphabetMap (FactorConservation)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (Injection)
open ForcingConditionGraphs (function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- All target elements, not merely the image of the old carrier. -/
def Intersections (D N mul mulN f : M.Carrier .set) : Prop := ∀ x y j fx fy fj,
  PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
  PureKuratowski.PairMember M j fj f → JoinProperty D mul x y j → JoinProperty N mulN fx fy fj

def Common (D N mul mulN f : M.Carrier .set) : Prop := ∀ x y fx fy,
  PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
  (∃ z, (Project.FirstOrderSemantics.reduct M).mem z N ∧ Divides N mulN fx z ∧ Divides N mulN fy z) →
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧ Divides D mul x z ∧ Divides D mul y z

/-- Exact four fields of Conservative; homomorphism laws are supplied separately,
as they are by the MonoidHom argument in the source. -/
def Conservative (D N mul mulN f : M.Carrier .set) : Prop :=
  Injection D N f ∧ FactorConservation N mulN f ∧ Intersections D N mul mulN f ∧ Common D N mul mulN f

theorem headDiv_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e node F projection x y j q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hCone : ConeLaws w D mul e zero node F S projection A)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j D)
    (hJoin : JoinProperty D mul x y j) (hq : Raw w D S q) :
    (HeadDiv w D S zero mul A x q ∧ HeadDiv w D S zero mul A y q) ↔ HeadDiv w D S zero mul A j q := by
  rcases cases_raw hM hw hz hzw hq with ⟨z,hOld⟩ | ⟨s,t,hCons⟩
  · simp only [headDiv_old_iff hz hOld]
    exact hJoin z hOld.1
  · simp only [headDiv_cons_iff hM hw hz hCons]
    exact hCone.2.2.2.1 x y j s hx hy hj hJoin

theorem headDiv_common (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e node F projection x y q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hCone : ConeLaws w D mul e zero node F S projection A)
    (hq : Raw w D S q) (hx : HeadDiv w D S zero mul A x q) (hy : HeadDiv w D S zero mul A y q) :
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧ Divides D mul x z ∧ Divides D mul y z := by
  rcases cases_raw hM hw hz hzw hq with ⟨z,hOld⟩ | ⟨s,t,hCons⟩
  · exact ⟨z,hOld.1,(headDiv_old_iff hz hOld).mp hx,(headDiv_old_iff hz hOld).mp hy⟩
  · exact hCone.2.2.2.2.1 x y s (cons_letter hCons)
      ((headDiv_cons_iff hM hw hz hCons).mp hx) ((headDiv_cons_iff hM hw hz hCons).mp hy)

theorem old_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W e node F projection G unit H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hCone : ConeLaws w D mul e zero node F S projection A) (hW : WordCarrier w D S mul A b W)
    (hH : OldGraph zero D H) (hInj : Injection D W H)
    (hEmb : EmbeddingLaws w D S zero mul A W G e unit H) : Conservative D W mul G H := by
  refine ⟨hInj,?_,?_,?_⟩
  · intro x y z ox oy hx hy hzW hp
    obtain ⟨t,ht,_⟩ := (hEmb.2.2.1 x y ox oy z hx hy hzW).mp hp
    exact ⟨t,(hH t z).mpr ht⟩
  · intro x y j ox oy oj hx hy hj hJoin q hq
    change (Divides W G ox q ∧ Divides W G oy q) ↔ Divides W G oj q
    rw [hEmb.2.2.2.2 x ox q hx hq,hEmb.2.2.2.2 y oy q hy hq,hEmb.2.2.2.2 j oj q hj hq]
    exact headDiv_intersection hM hw hz hzw hCone (function_input hInj.1.1 hx)
      (function_input hInj.1.1 hy) (function_input hInj.1.1 hj) hJoin (word_raw hW hq)
  · intro x y ox oy hx hy hCommon
    obtain ⟨q,hq,hxq,hyq⟩ := hCommon
    exact headDiv_common hM hw hz hzw hCone (word_raw hW hq)
      ((hEmb.2.2.2.2 x ox q hx hq).mp hxq) ((hEmb.2.2.2.2 y oy q hy hq).mp hyq)

theorem exists_conservative_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit node F projection : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hCone : ConeLaws w D mul e zero node F S projection A) :
    ∃ H, OldGraph zero D H ∧ EmbeddingLaws w D S zero mul A W G e unit H ∧ Conservative D W mul G H := by
  obtain ⟨H,hInj,hH⟩ := exists_old_graph hM hz hzw hW
  have hEmb := embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hG hH
  exact ⟨H,hH,hEmb,old_conservative hM hw hz hzw hCone hW hH hInj hEmb⟩

end PPAC.Migration.ConstructionProbeConservative
