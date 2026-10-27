/- Pinned MergerWords.root:568 / root_mul_old:571 /
root_mul_eq_iff:580 / root_not_old:587. Construct the actual root graph;
its multiplication realizes exactly the original prescribed relation.
Consumer: original MergerData.root/realization and ConservativeCells.Merger. -/
import PPAC.Migration.ConstructionMergerOldEmbedding

namespace PPAC.Migration.ConstructionMergerRoots
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_indices)
open ConstructionProbeOldEmbedding (OldGraph)
open ConstructionMergerCopies (EqualityLaw copy_eq_iff)
open ConstructionMergerAction (CopyLaw)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Root (w D L e projection unit i r : M.Carrier .set) : Prop :=
  ∃ c, Product projection i e c ∧ Cons w D L c unit r

def RootGraph (w D L e projection unit F : M.Carrier .set) : Prop := ∀ i r,
  PureKuratowski.PairMember M i r F ↔ Root w D L e projection unit i r

def root {m0 : Nat} (w D L e projection unit i r : Fin m0) : Project.Formula 1 m0 :=
  .existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ i.succ e.succ 0))
    (ConstructionProbeRaw.cons w.succ D.succ L.succ 0 unit.succ r.succ))

theorem root_freeClosed {m0 : Nat} (w D L e projection unit i r : Fin m0) : (root w D L e projection unit i r).FreeClosed := by
  simp -implicitDefEqProofs [root,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.cons_freeClosed]

theorem root_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L e projection unit i r : Fin m0) :
    Project.Formula.satisfies env (root w D L e projection unit i r) ↔ Root (env.bound w) (env.bound D) (env.bound L) (env.bound e) (env.bound projection) (env.bound unit) (env.bound i) (env.bound r) := by
  simp only [root,Root,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),ConstructionProbeRaw.cons_semantics hM]
  rfl

def rootGraph {m0 : Nat} (w D L e projection unit F : Fin m0) : Project.Formula 1 m0 :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 1 0))
    (root w.succ.succ D.succ.succ L.succ.succ e.succ.succ projection.succ.succ unit.succ.succ 1 0)))

theorem rootGraph_freeClosed {m0 : Nat} (w D L e projection unit F : Fin m0) : (rootGraph w D L e projection unit F).FreeClosed := by
  simp -implicitDefEqProofs [rootGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,root_freeClosed]

theorem rootGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L e projection unit F : Fin m0) :
    Project.Formula.satisfies env (rootGraph w D L e projection unit F) ↔ RootGraph (env.bound w) (env.bound D) (env.bound L) (env.bound e) (env.bound projection) (env.bound unit) (env.bound F) := by
  simp only [rootGraph,RootGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,root_semantics hM]
  rfl

theorem exists_root_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D L zero mul e C W projection unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hW : Carrier w D L W)
    (hC : Representatives n D C) (hp : MapsTo C L projection) (hUnit : Old zero D e unit) :
    ∃ F, MapsTo n W F ∧ RootGraph w D L e projection unit F := by
  let schema : Project.BinarySchema 6 := { body := root 2 3 4 5 6 7 1 0,freeClosed := root_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := fun i => match i with | 0 => w | 1 => D | 2 => L | 3 => e | 4 => projection | _ => unit,
    free := fun _ => w }
  have he (i r) : schema.denote env i r ↔ Root w D L e projection unit i r :=
    root_semantics hM ((env.push i).push r) 2 3 4 5 6 7 1 0
  obtain ⟨F,hF,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := n) (target := W) (by
      intro i hi
      obtain ⟨c,hc,hic⟩ := projected hM hC hp hi hm.1.1
      obtain ⟨r,hr⟩ := ConstructionProbeRaw.exists_cons hM hw hc (ConstructionProbeRaw.old_raw hM hz hzw hUnit)
      exact ⟨r,(he i r).mpr ⟨c,hic,hr⟩⟩) (by
      intro i _ r r' hr hr'
      obtain ⟨c,hc,hCons⟩ := (he i r).mp hr
      obtain ⟨c',hc',hCons'⟩ := (he i r').mp hr'
      have hEq := ConstructionProbeHomEvaluation.product_unique hM hp hc hc'
      subst c'
      exact ConstructionProbeRaw.cons_unique hM hw hCons hCons') (by
      intro i r _ hr
      obtain ⟨c,_,hCons⟩ := (he i r).mp hr
      exact (hW r).mpr (ConstructionProbeRaw.cons_raw hCons).2)
  refine ⟨F,(ForcingSupportSize.native_mapsTo hM n W F).mpr hF,?_⟩
  intro i r
  refine (hgraph i r).trans ⟨fun h => (he i r).mp h.2,fun hr => ?_⟩
  obtain ⟨c,hc,hCons⟩ := hr
  exact ⟨(projected_indices hC hp hc).1,(he i r).mpr ⟨c,hc,hCons⟩⟩

theorem root_mul_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e T H projection unit i r x ox out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hm : LeftCancelMonoid D mul e) (hCopy : CopyLaw D mul projection A)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hRoot : Root w D L e projection unit i r) (hOld : Old zero D x ox) :
    Product H r ox out ↔ ∃ c, Product projection i x c ∧ Cons w D L c unit out := by
  obtain ⟨c,hProj,hConsRoot⟩ := hRoot
  have hEx : Product mul e x x := ((hm.1.2 x hOld.1 x).1).mpr rfl
  rw [hLaws.1 x r ox out hOld]
  constructor
  · intro hAct
    have hv := (hTable r x out).mp hAct
    rcases hv.2 with ⟨a,ax,hOldR,_,_⟩ | ⟨s,t,sm,hSnoc,hSm,hOut⟩
    · exact (ConstructionProbeRaw.old_ne_cons hz hOldR hConsRoot).elim
    · obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hSnoc hConsRoot
      exact ⟨sm,(hCopy i e x s x sm hOld.1 hProj hEx).mp hSm,hOut⟩
  · rintro ⟨cx,hCx,hOut⟩
    exact (hTable r x out).mpr ⟨hOld.1,Or.inr ⟨c,unit,cx,hConsRoot,
      (hCopy i e x c x cx hOld.1 hProj hEx).mpr hCx,hOut⟩⟩

def RootLaws (w D L n mul P projection unit H O F : M.Carrier .set) : Prop :=
  (∀ i r x ox out, PureKuratowski.PairMember M i r F → PureKuratowski.PairMember M x ox O →
    (Product H r ox out ↔ ∃ c, Product projection i x c ∧ Cons w D L c unit out)) ∧
  (∀ i j x y ri rj ox oy u v, PureKuratowski.PairMember M i ri F → PureKuratowski.PairMember M j rj F →
    PureKuratowski.PairMember M x ox O → PureKuratowski.PairMember M y oy O →
    Product H ri ox u → Product H rj oy v → (u = v ↔ ConstructionMergerRelations.CopyRel n D mul P i x j y)) ∧
  (∀ i r x, PureKuratowski.PairMember M i r F → ¬ PureKuratowski.PairMember M x r O)

theorem root_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L n zero mul A e P T H projection unit O F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hm : LeftCancelMonoid D mul e) (hCopy : CopyLaw D mul projection A)
    (hEq : EqualityLaw n D mul P projection) (hTable : ActionTable w D L zero mul A T)
    (hLaws : Laws w D L zero T H) (hO : OldGraph zero D O) (hRoots : RootGraph w D L e projection unit F) :
    RootLaws w D L n mul P projection unit H O F := by
  refine ⟨?_,?_,?_⟩
  · intro i r x ox out hr hx
    exact root_mul_old hM hw hz hm hCopy hTable hLaws ((hRoots i r).mp hr) ((hO x ox).mp hx)
  · intro i j x y ri rj ox oy u v hri hrj hx hy hu hv
    obtain ⟨cx,hCx,hU⟩ := (root_mul_old hM hw hz hm hCopy hTable hLaws ((hRoots i ri).mp hri) ((hO x ox).mp hx)).mp hu
    obtain ⟨cy,hCy,hV⟩ := (root_mul_old hM hw hz hm hCopy hTable hLaws ((hRoots j rj).mp hrj) ((hO y oy).mp hy)).mp hv
    constructor
    · intro he
      have hCeq := (ConstructionProbeRaw.cons_injective hM hw hU (he.symm ▸ hV)).1
      exact (copy_eq_iff hEq hCx hCy).mp hCeq
    · intro hRel
      have hCeq := (copy_eq_iff hEq hCx hCy).mpr hRel
      subst cy
      exact ConstructionProbeRaw.cons_unique hM hw hU hV
  · intro i r x hr hx
    obtain ⟨c,_,hCons⟩ := (hRoots i r).mp hr
    exact ConstructionProbeRaw.old_ne_cons hz ((hO x r).mp hx) hCons

def rootLaws {m0 : Nat} (w D L n mul P projection unit H O F : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ 4 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ 2 1)) (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ 3 1 0)) (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ.succ 5 3 0)) (ConstructionProbeRaw.cons w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ.succ 0 unit.succ.succ.succ.succ.succ.succ 1))))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 5)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 4)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 2)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5 3 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4 2 0)) (.iff (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (ConstructionMergerRelations.rel n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 7 8 6)))))))))))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 2 1)) (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ 0 1)))))))))

theorem rootLaws_freeClosed {m0 : Nat} (w D L n mul P projection unit H O F : Fin m0) :
    (rootLaws w D L n mul P projection unit H O F).FreeClosed := by
  simp -implicitDefEqProofs [rootLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,ConstructionMergerRelations.rel_freeClosed,ConstructionProbeRaw.cons_freeClosed]

theorem rootLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L n mul P projection unit H O F : Fin m0) :
    Project.Formula.satisfies env (rootLaws w D L n mul P projection unit H O F) ↔
      RootLaws (env.bound w) (env.bound D) (env.bound L) (env.bound n) (env.bound mul) (env.bound P) (env.bound projection) (env.bound unit) (env.bound H) (env.bound O) (env.bound F) := by
  simp only [rootLaws,RootLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,product_semantics (M := M),
    ConstructionProbeRaw.cons_semantics hM,ConstructionMergerRelations.rel_semantics hM]
  rfl

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
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ ConstructionMergerCopyCones.HasConeJoins D L A ∧ ConstructionProbeSharedIntersections.ConditionalJoins W H ∧ ∃ O, OldGraph zero D O ∧ ConstructionProbeConservative.Conservative D W mul H O ∧
      ConstructionProbeLiftHom.PreservesProducts mul H O ∧ ConstructionPersistentProfiles.HasOldGates D W mul H O ∧ PureKuratowski.PairMember M e unit O ∧
      (∀ a b d p node, ConstructionPersistentProfiles.ProbeProfile w D mul a b d p node →
        ∃ mapped fa fb fd fp, ConstructionProbeMappedPath.NodeMap node O mapped ∧
          PureKuratowski.PairMember M a fa O ∧ PureKuratowski.PairMember M b fb O ∧
          PureKuratowski.PairMember M d fd O ∧ PureKuratowski.PairMember M p fp O ∧
          ConstructionPersistentProfiles.ProbeProfile w W H fa fb fd fp mapped) ∧ ∃ F, MapsTo n W F ∧ RootGraph w D L e projection unit F ∧ RootLaws w D L n mul P projection unit H O F := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles⟩ :=
    ConstructionMergerOldEmbedding.exists_system hM hw hz hzw hm hc hJoins hP hValid
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hParent
  obtain ⟨F,hF,hRoots⟩ := exists_root_graph hM hw hz hzw hm hW hC hp hUnit
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,hCone,hJoinsW,
    O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,
    root_laws hM hw hz hm hCopy hEq hWordTable hLaws hO hRoots⟩

end PPAC.Migration.ConstructionMergerRoots
