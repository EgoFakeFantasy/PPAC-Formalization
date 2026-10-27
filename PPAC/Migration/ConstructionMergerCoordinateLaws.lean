/- Pinned MergerCones coordinate bounds:118-147, representation persistence:152,
coordinate height monotonicity:159 and represented strictness:176.
Construct both actual coordinate tables on SAME Merger copies; old strictness
comes from accepted UniformMargins, not a new monotonicity oracle.
Consumer: literal copiesHeight finite average / copiesCost finite product. -/
import PPAC.Migration.ConstructionMergerCoordinates

namespace PPAC.Migration.ConstructionMergerCoordinateLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected_indices)
open ConstructionMergerCopies (EqualityLaw)
open ConstructionMergerAction (CopyLaw)
open ConstructionMergerCopyCones (Reaches reaches_same_copy_iff)
open ConstructionMergerCoordinates (HasRep Value Graph graph_copy_iff hasRep_of_reaches)
open ConstructionRealCuts (Subset CutCarrier)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeLetterIntervals (UniformMargins)
open ConstructionProbeLetterFloor (HeightOrder)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem empty_cut_mem (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero top : M.Carrier .set} (hR : CutCarrier hM w Q R)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (htop : (Project.FirstOrderSemantics.reduct M).mem top R) :
    (Project.FirstOrderSemantics.reduct M).mem zero R := by
  obtain ⟨q,hq,_⟩ := ((hR top).mp htop).2.2.2
  apply (hR zero).mpr
  exact ⟨fun p hp => (hz p hp).elim,fun p q hq _ => (hz q hq).elim,
    fun p hp => (hz p hp).elim,q,hq,hz q⟩

theorem coordinate_bounds {n L projection Height Cost zero top CH CC : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hTop : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top)
    (hHB : ConstructionCutWeights.RangeBound top Height) (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hCH : Graph n L projection Height zero CH) (hCC : Graph n L projection Cost top CC) :
    (∀ i z a, Product CH i z a → Subset zero a ∧ Strict a top) ∧
      (∀ i z a, Product CC i z a → (∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) ∧ Subset a top) := by
  constructor
  · intro i z a ha
    refine ⟨fun p hp => (hz p hp).elim,?_⟩
    rcases ((hCH i z a).mp ha).2.2 with ⟨x,_,hxa⟩ | ⟨_,rfl⟩
    · exact (hHB x a hxa).2
    · refine ⟨fun p hp => (hz p hp).elim,?_⟩
      intro h
      obtain ⟨p,hp⟩ := hTop
      exact hz p (h p hp)
  · intro i z a ha
    rcases ((hCC i z a).mp ha).2.2 with ⟨x,_,hxa⟩ | ⟨_,rfl⟩
    · exact hCB x a hxa
    · exact ⟨hTop,fun _ hp => hp⟩

theorem coordHeight_mono
    {n D L mul e P C R projection A Height zero CH i z v a b : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hCopy : CopyLaw D mul projection A)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hOrder : HeightOrder D mul R Height) (hCH : Graph n L projection Height zero CH)
    (ha : Product CH i z a) (hb : Product CH i v b) (hzv : Reaches D A z v) : Subset a b := by
  by_cases hRep : HasRep projection i z
  · obtain ⟨x,hx⟩ := hRep
    obtain ⟨y,hy⟩ := hasRep_of_reaches hm hC hp hCopy ⟨x,hx⟩ hzv
    have hxa := (graph_copy_iff hC hp hEq hCH hx).mp ha
    have hyb := (graph_copy_iff hC hp hEq hCH hy).mp hb
    exact hOrder.2.2 x y a b hxa hyb ((reaches_same_copy_iff hm hC hp hEq hCopy hx hy).mp hzv)
  · rcases ((hCH i z a).mp ha).2.2 with ⟨x,hx,_⟩ | ⟨_,rfl⟩
    · exact (hRep ⟨x,hx⟩).elim
    · exact fun p hp => (hz p hp).elim

theorem coordHeight_strict (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n D L mul e P C R projection A Height Cost zero CH i z v a b : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hCopy : CopyLaw D mul projection A)
    (hR : CutCarrier hM w Q R) (hHeight : MapsTo D R Height)
    (hUniform : UniformMargins hM w Q D mul Height Cost) (hCH : Graph n L projection Height zero CH)
    (ha : Product CH i z a) (hb : Product CH i v b) (hzv : Reaches D A z v) (hne : z ≠ v)
    (hRep : HasRep projection i z) : Strict a b := by
  obtain ⟨x,hx⟩ := hRep
  obtain ⟨y,hy⟩ := hasRep_of_reaches hm hC hp hCopy ⟨x,hx⟩ hzv
  have hxa := (graph_copy_iff hC hp hEq hCH hx).mp ha
  have hyb := (graph_copy_iff hC hp hEq hCH hy).mp hb
  have hxy := (reaches_same_copy_iff hm hC hp hEq hCopy hx hy).mp hzv
  have hnyx : ¬ ConstructionBaseMonoid.Divides D mul y x := by
    intro hyx
    have he := ConstructionProbeGateCap.divides_antisymm hm hc (projected_indices hC hp hx).2 hxy hyx
    subst y
    exact hne (ConstructionProbeHomEvaluation.product_unique hM hp hx hy)
  obtain ⟨cap,sum,_,hSum,hStrict,_⟩ := hUniform x y a b hxa hyb hxy hnyx
  have haCut := (hR a).mp (hHeight.2 x a hxa)
  have hIncl : Subset a sum := fun p hpa => (hSum p).mpr ⟨haCut.1 p hpa,Or.inl hpa⟩
  exact ConstructionProbeIntervals.le_strict_trans hIncl hStrict

def Laws (n D L A projection Height Cost zero top CH CC : M.Carrier .set) : Prop :=
  (∀ i x z c, Product projection i x z →
    (Product CH i z c ↔ PureKuratowski.PairMember M x c Height) ∧
    (Product CC i z c ↔ PureKuratowski.PairMember M x c Cost)) ∧
  (∀ i z, (Project.FirstOrderSemantics.reduct M).mem i n → (Project.FirstOrderSemantics.reduct M).mem z L →
    ¬ HasRep projection i z → Product CH i z zero ∧ Product CC i z top) ∧
  (∀ i z a, Product CH i z a → Subset zero a ∧ Strict a top) ∧
  (∀ i z a, Product CC i z a → (∃ p, (Project.FirstOrderSemantics.reduct M).mem p a) ∧ Subset a top) ∧
  (∀ i z v, HasRep projection i z → Reaches D A z v → HasRep projection i v) ∧
  (∀ i z v a b, Product CH i z a → Product CH i v b → Reaches D A z v → Subset a b) ∧
  (∀ i z v a b, Product CH i z a → Product CH i v b → Reaches D A z v → z ≠ v → HasRep projection i z → Strict a b)

theorem coordinate_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n D L mul e P C R projection A Height Cost zero top CH CC : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hCopy : CopyLaw D mul projection A)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hTop : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top)
    (hR : CutCarrier hM w Q R) (hHeight : MapsTo D R Height)
    (hHB : ConstructionCutWeights.RangeBound top Height) (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hUniform : UniformMargins hM w Q D mul Height Cost)
    (hCH : Graph n L projection Height zero CH) (hCC : Graph n L projection Cost top CC) :
    Laws n D L A projection Height Cost zero top CH CC := by
  have hBounds := coordinate_bounds hz hTop hHB hCB hCH hCC
  have hOrder := ConstructionProbeParent.height_order hM hm hc hR hHeight hHB hUniform
  refine ⟨?_,?_,hBounds.1,hBounds.2,?_,?_,?_⟩
  · intro i x z c hx
    exact ⟨graph_copy_iff hC hp hEq hCH hx,graph_copy_iff hC hp hEq hCC hx⟩
  · intro i z hi hzL hn
    exact ⟨(hCH i z zero).mpr ⟨hi,hzL,Or.inr ⟨hn,rfl⟩⟩,(hCC i z top).mpr ⟨hi,hzL,Or.inr ⟨hn,rfl⟩⟩⟩
  · intro i z v hRep hReach
    exact hasRep_of_reaches hm hC hp hCopy hRep hReach
  · intro i z v a b ha hb hReach
    exact coordHeight_mono hm hC hp hEq hCopy hz hOrder hCH ha hb hReach
  · intro i z v a b ha hb hReach hne hRep
    exact coordHeight_strict hM hm hc hC hp hEq hCopy hR hHeight hUniform hCH ha hb hReach hne hRep

def laws {m0 : Nat} (n D L A projection Height Cost zero top CH CC : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ.succ 3 2 1)) (.conj (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ.succ.succ 3 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge Height.succ.succ.succ.succ 2 0))) (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product CC.succ.succ.succ.succ 3 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge Cost.succ.succ.succ.succ 2 0))))))))) (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound n.succ.succ)) (.imp (.mem (.bound 0) (.bound L.succ.succ)) (.imp (.neg (ConstructionMergerCoordinates.hasRep projection.succ.succ 1 0)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ 1 0 zero.succ.succ)) (ProjectSyntax.encode id (ForcingDiagramOrder.product CC.succ.succ 1 0 top.succ.succ)))))))) (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ.succ 2 1 0)) (.conj (Project.Formula.subset (.bound zero.succ.succ.succ) (.bound 0)) (.conj (Project.Formula.subset (.bound 0) (.bound top.succ.succ.succ)) (.neg (Project.Formula.subset (.bound top.succ.succ.succ) (.bound 0))))))))) (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product CC.succ.succ.succ 2 1 0)) (.conj (.existsE (.mem (.bound 0) (.bound 1))) (Project.Formula.subset (.bound 0) (.bound top.succ.succ.succ))))))) (.conj (.forallE (.forallE (.forallE (.imp (ConstructionMergerCoordinates.hasRep projection.succ.succ.succ 2 1) (.imp (ConstructionMergerCopyCones.reaches D.succ.succ.succ A.succ.succ.succ 1 0) (ConstructionMergerCoordinates.hasRep projection.succ.succ.succ 2 0)))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ.succ.succ.succ 4 2 0)) (.imp (ConstructionMergerCopyCones.reaches D.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 3 2) (Project.Formula.subset (.bound 1) (.bound 0)))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product CH.succ.succ.succ.succ.succ 4 2 0)) (.imp (ConstructionMergerCopyCones.reaches D.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 3 2) (.imp (.neg (Project.Formula.extensionalEq (.bound 3) (.bound 2))) (.imp (ConstructionMergerCoordinates.hasRep projection.succ.succ.succ.succ.succ 4 3) (.conj (Project.Formula.subset (.bound 1) (.bound 0)) (.neg (Project.Formula.subset (.bound 0) (.bound 1))))))))))))))))))))

theorem laws_freeClosed {m0 : Nat} (n D L A projection Height Cost zero top CH CC : Fin m0) :
    (laws n D L A projection Height Cost zero top CH CC).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,
    ConstructionMergerCoordinates.hasRep_freeClosed,ConstructionMergerCopyCones.reaches_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (n D L A projection Height Cost zero top CH CC : Fin m0) :
    Project.Formula.satisfies env (laws n D L A projection Height Cost zero top CH CC) ↔
      Laws (env.bound n) (env.bound D) (env.bound L) (env.bound A) (env.bound projection) (env.bound Height) (env.bound Cost) (env.bound zero) (env.bound top) (env.bound CH) (env.bound CC) := by
  simp only [laws,Laws,ConstructionProbeIntervals.Strict,ConstructionRealCuts.Subset,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),ConstructionMergerCoordinates.hasRep_semantics hM,
    ConstructionMergerCopyCones.reaches_semantics hM]
  rfl

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero Q R Height Cost top : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hR : CutCarrier hM w Q R) (hHeight : MapsTo D R Height)
    (hHB : ConstructionCutWeights.RangeBound top Height) (hCost : MapsTo D R Cost)
    (hCB : ConstructionProbeGateCap.Bounds top Cost) (htop : (Project.FirstOrderSemantics.reduct M).mem top R)
    (hUniform : UniformMargins hM w Q D mul Height Cost) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ ConstructionProbeRaw.Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ ConstructionMergerWordProduct.Laws w D L zero T H) ∧
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ ConstructionMergerCopyCones.HasConeJoins D L A ∧ ConstructionProbeSharedIntersections.ConditionalJoins W H ∧ ∃ O, ConstructionProbeOldEmbedding.OldGraph zero D O ∧ ConstructionProbeConservative.Conservative D W mul H O ∧
      ConstructionProbeLiftHom.PreservesProducts mul H O ∧ ConstructionPersistentProfiles.HasOldGates D W mul H O ∧ PureKuratowski.PairMember M e unit O ∧
      (∀ a b d p node, ConstructionPersistentProfiles.ProbeProfile w D mul a b d p node →
        ∃ mapped fa fb fd fp, ConstructionProbeMappedPath.NodeMap node O mapped ∧
          PureKuratowski.PairMember M a fa O ∧ PureKuratowski.PairMember M b fb O ∧
          PureKuratowski.PairMember M d fd O ∧ PureKuratowski.PairMember M p fp O ∧
          ConstructionPersistentProfiles.ProbeProfile w W H fa fb fd fp mapped) ∧ ∃ F, MapsTo n W F ∧ ConstructionMergerRoots.RootGraph w D L e projection unit F ∧ ConstructionMergerRoots.RootLaws w D L n mul P projection unit H O F ∧ ∃ J CH CC, Representatives n L J ∧ MapsTo J R CH ∧ MapsTo J R CC ∧
      Graph n L projection Height zero CH ∧ Graph n L projection Cost top CC ∧
      Laws n D L A projection Height Cost zero top CH CC := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws⟩ :=
    ConstructionMergerRoots.exists_system hM hw hz hzw hm hc hJoins hP hValid
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hParent
  obtain ⟨he,hHE,_⟩ := hHeight.1.2 e hm.1.1
  obtain ⟨p,hpHeight⟩ := (hHB e he hHE).1
  have hTop : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top := ⟨p,(hHB e he hHE).2.1 p hpHeight⟩
  have hZero := empty_cut_mem hM hR hz htop
  obtain ⟨J,hJ⟩ := ConstructionProbeLetters.exists_representatives hM n L
  obtain ⟨CH,hCH,hCHGraph⟩ := ConstructionMergerCoordinates.exists_graph hM hC hp hEq hHeight hZero hJ
  obtain ⟨CC,hCC,hCCGraph⟩ := ConstructionMergerCoordinates.exists_graph hM hC hp hEq hCost htop hJ
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,hCone,hJoinsW,
    O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCHGraph,hCCGraph,
    coordinate_laws hM hm hc hC hp hEq hCopy hz hTop hR hHeight hHB hCB hUniform hCHGraph hCCGraph⟩

end PPAC.Migration.ConstructionMergerCoordinateLaws
