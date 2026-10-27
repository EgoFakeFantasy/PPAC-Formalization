/- Pinned ConservativeExtensions.Word.oldHom_conservative:104,
PersistentProfiles.Word.hasOldGates:134 / preserve_profile:140.
Construct actual old graph on SAME Merger Word. Reuse existing Conservative,
HasOldGates, product preservation and profile mapping, not Probe's special laws.
Consumer: original MergerData.inclusion / no_new_old_divisors / preserves_profile. -/
import PPAC.Migration.ConstructionMergerWordCones
import PPAC.Migration.ConstructionProbeConservativeSyntax
import PPAC.Migration.ConstructionPersistentProfiles
import PPAC.Migration.ConstructionProbeLiftHomSyntax

namespace PPAC.Migration.ConstructionMergerOldEmbedding
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeOldEmbedding (OldGraph)
open ConstructionProbeConservative (Conservative)
open ConstructionPersistentProfiles (HasOldGates ProbeProfile)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem exists_old_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero W : M.Carrier .set}
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) : ∃ O, Injection D W O ∧ OldGraph zero D O := by
  let schema : Project.BinarySchema 2 := {
    body := ConstructionProbeRaw.old 2 3 1 0,freeClosed := ConstructionProbeRaw.old_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases zero (fun _ => D),free := fun _ => zero }
  have he (x q : M.Carrier .set) : schema.denote env x q ↔ Old zero D x q :=
    ConstructionProbeRaw.old_semantics hM ((env.push x).push q) 2 3 1 0
  obtain ⟨O,hO,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := D) (target := W) (by
      intro x hx
      obtain ⟨q,hq⟩ := ConstructionProbeRaw.exists_old hM hx (zero := zero)
      exact ⟨q,(he x q).mpr hq⟩) (by
      intro x _ q r hq hr
      exact ConstructionProbeRaw.old_unique hM ((he x q).mp hq) ((he x r).mp hr)) (by
      intro x q _ hq
      exact (hW q).mpr (ConstructionProbeRaw.old_raw hM hz hzw ((he x q).mp hq)))
  have hg : OldGraph zero D O := fun x q => (hgraph x q).trans
    ⟨fun h => (he x q).mp h.2,fun h => ⟨h.1,(he x q).mpr h⟩⟩
  exact ⟨O,⟨(ForcingSupportSize.native_mapsTo hM D W O).mpr hO,
    fun x y q hx hy => ConstructionProbeRaw.old_injective ((hg x q).mp hx) ((hg y q).mp hy)⟩,hg⟩

theorem preserves_products {w D L zero mul A T H O : M.Carrier .set}
    (hO : OldGraph zero D O) (hTable : ActionTable w D L zero mul A T)
    (hLaws : Laws w D L zero T H) : PreservesProducts mul H O := by
  intro x y z ox oy oz hp hx hy hz
  have hX := (hO x ox).mp hx
  have hY := (hO y oy).mp hy
  have hZ := (hO z oz).mp hz
  exact (hLaws.1 y ox oy oz hY).mpr ((hTable ox y oz).mpr ⟨hY.1,Or.inl ⟨x,z,hX,hp,hZ⟩⟩)

theorem old_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hInj : Injection D W O) (hO : OldGraph zero D O) : Conservative D W mul H O := by
  refine ⟨hInj,?_,?_,?_⟩
  · intro x y z ox oy _ hy _ hp
    obtain ⟨_,t,_,hT,_⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hH hTable hLaws ((hO y oy).mp hy) hp
    exact ⟨t,(hO t z).mpr hT⟩
  · intro x y j ox oy oj hx hy hj hJoin
    exact ConstructionMergerWordDivisibility.preserve_old_cone_intersection hM hw hz hzw hW hB hH hTable hLaws
      ((hO x ox).mp hx) ((hO y oy).mp hy) ((hO j oj).mp hj) hJoin
  · intro x y ox oy hx hy hCommon
    exact (ConstructionMergerWordDivisibility.old_common_multiple_iff hM hw hz hzw hW hB hH hTable hLaws
      ((hO x ox).mp hx) ((hO y oy).mp hy)).mp hCommon

theorem has_old_gates (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hO : OldGraph zero D O) : HasOldGates D W mul H O := by
  intro q _ hCommon
  obtain ⟨a,oa,ha,r,_,hp⟩ := hCommon
  obtain ⟨x,_,hX,_,_⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hH hTable hLaws ((hO a oa).mp ha) hp
  exact Or.inl ⟨x,(hO x q).mpr hX⟩

theorem preserves_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D W mul H e unit O a b d p node : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmW : LeftCancelMonoid W H unit)
    (hCon : Conservative D W mul H O) (hPres : PreservesProducts mul H O)
    (hGates : HasOldGates D W mul H O) (hProfile : ProbeProfile w D mul a b d p node) :
    ∃ mapped fa fb fd fp, NodeMap node O mapped ∧
      PureKuratowski.PairMember M a fa O ∧ PureKuratowski.PairMember M b fb O ∧
      PureKuratowski.PairMember M d fd O ∧ PureKuratowski.PairMember M p fp O ∧
      ProbeProfile w W H fa fb fd fp mapped :=
  ConstructionPersistentProfiles.exists_mapped_profile hM hm hmW hCon hPres hGates hProfile

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ Laws w D L zero T H) ∧
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ ConstructionMergerCopyCones.HasConeJoins D L A ∧ ConstructionProbeSharedIntersections.ConditionalJoins W H ∧ ∃ O, OldGraph zero D O ∧ Conservative D W mul H O ∧
      PreservesProducts mul H O ∧ HasOldGates D W mul H O ∧ PureKuratowski.PairMember M e unit O ∧
      (∀ a b d p node, ProbeProfile w D mul a b d p node →
        ∃ mapped fa fb fd fp, NodeMap node O mapped ∧
          PureKuratowski.PairMember M a fa O ∧ PureKuratowski.PairMember M b fb O ∧
          PureKuratowski.PairMember M d fd O ∧ PureKuratowski.PairMember M p fp O ∧
          ProbeProfile w W H fa fb fd fp mapped) := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW⟩ :=
    ConstructionMergerWordCones.exists_system hM hw hz hzw hm hc hJoins hP hValid
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hParent
  obtain ⟨O,hInj,hO⟩ := exists_old_graph hM hz hzw hW
  have hCons := old_conservative hM hw hz hzw hW hB hH hWordTable hLaws hInj hO
  have hPres := preserves_products hO hWordTable hLaws
  have hGates := has_old_gates hM hw hz hzw hW hB hH hWordTable hLaws hO
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,hCone,hJoinsW,
    O,hO,hCons,hPres,hGates,(hO e unit).mpr hUnit,fun a b d p node hProfile =>
      preserves_profile hM hm hMonoid hCons hPres hGates hProfile⟩

end PPAC.Migration.ConstructionMergerOldEmbedding
