/- Pinned CellTowers.Attachment.finite_coefficients:203-219.
Transport the same finite coefficient set along the literal attachment map.
The inverse-image submonoid uses native Separation; graph composition and
range use the already existing native constructors. -/
import PPAC.Migration.ConstructionCellCoefficients
import PPAC.Migration.ForcingSupportedNames

namespace PPAC.Migration.ConstructionAttachmentCoefficients
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCellGeneration
open ConstructionCellCoefficients (Coefficients Finite coefficients_bound)
open ConstructionRealCuts (Subset)
open ConstructionProbePushout (Hom)
open ConstructionProbeMappedPath (NodeMap exists_node_map)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (IdentityGraph function_input function_unique)
open ForcingSupportedNames (Range)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def preimageMember {m : Nat} (W F S x : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound x) (.bound W))
    (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ x.succ 0))
      (.mem (.bound 0) (.bound S.succ))))

theorem preimageMember_freeClosed {m : Nat} (W F S x : Fin m) :
    (preimageMember W F S x).FreeClosed := by
  simp [preimageMember,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem preimageMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W F S x : Fin m) :
    Project.Formula.satisfies env (preimageMember W F S x) ↔
      (Project.FirstOrderSemantics.reduct M).mem (env.bound x) (env.bound W) ∧
      ∀ y, PureKuratowski.PairMember M (env.bound x) y (env.bound F) →
        (Project.FirstOrderSemantics.reduct M).mem y (env.bound S) := by
  simp only [preimageMember,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

/-- Source Q.comap of the actual homomorphism, constructed as an internal set. -/
theorem exists_comap (hM : FirstOrder.Theory.Models M nativeZF)
    {W V G H unit e F S : M.Carrier .set}
    (hWhole : Submonoid W G unit W) (hF : Hom W V G H unit e F)
    (hS : Submonoid V H e S) : ∃ Q, Submonoid W G unit Q ∧
      ∀ x, (Project.FirstOrderSemantics.reduct M).mem x Q ↔
        (Project.FirstOrderSemantics.reduct M).mem x W ∧
        ∀ y, PureKuratowski.PairMember M x y F → (Project.FirstOrderSemantics.reduct M).mem y S := by
  let schema : Project.UnarySchema 3 := {
    body := preimageMember 1 2 3 0
    freeClosed := preimageMember_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases W (Fin.cases F (fun _ => S))
    free := fun _ => W }
  obtain ⟨Q,hQ⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env W
  have hq x : (Project.FirstOrderSemantics.reduct M).mem x Q ↔
      (Project.FirstOrderSemantics.reduct M).mem x W ∧
      ∀ y, PureKuratowski.PairMember M x y F → (Project.FirstOrderSemantics.reduct M).mem y S := by
    have he := preimageMember_semantics hM (env.push x) 1 2 3 0
    exact (hQ x).trans ⟨fun h => he.mp h.2,fun h => ⟨h.1,he.mpr h⟩⟩
  refine ⟨Q,⟨fun x hx => ((hq x).mp hx).1,?_,?_⟩,hq⟩
  · refine (hq unit).mpr ⟨hWhole.2.1,?_⟩
    intro y hy
    have he := function_unique hF.1.1 hy hF.2.1
    exact he.symm ▸ hS.2.1
  · intro x y z hx hy hp
    obtain ⟨hxW,hxS⟩ := (hq x).mp hx
    obtain ⟨hyW,hyS⟩ := (hq y).mp hy
    refine (hq z).mpr ⟨hWhole.2.2 x y z hxW hyW hp,?_⟩
    intro fz hfz
    obtain ⟨fx,hfx,_⟩ := hF.1.1.2 x hxW
    obtain ⟨fy,hfy,_⟩ := hF.1.1.2 y hyW
    exact hS.2.2 fx fy fz (hxS fx hfx) (hyS fy hfy) (hF.2.2 x y z fx fy fz hp hfx hfy hfz)

/-- The exact closure membership is preserved, with the SAME old coefficient
set and both actual composite generator graphs. -/
theorem closure_image (hM : FirstOrder.Theory.Models M nativeZF)
    {D I W V G H unit e O P F old generators coefficients x y : M.Carrier .set}
    (hWhole : Submonoid W G unit W) (hO : MapsTo D W O) (hP : MapsTo I W P)
    (hF : Hom W V G H unit e F) (hOld : NodeMap O F old) (hGen : NodeMap P F generators)
    (hx : ClosureMember I W G unit O P coefficients x) (hxy : PureKuratowski.PairMember M x y F) :
    ClosureMember I V H e old generators coefficients y := by
  refine ⟨hF.1.2 x y hxy,?_⟩
  intro S hS ho hn
  obtain ⟨Q,hQ,hq⟩ := exists_comap hM hWhole hF hS
  have hOldQ : ImageIn coefficients O Q := by
    intro a u ha hau
    exact (hq u).mpr ⟨hO.2 a u hau,fun v huv => ho a v ha ((hOld a v).mpr ⟨u,hau,huv⟩)⟩
  have hNewQ : MapsTo I Q P := ⟨hP.1,fun i u hiu =>
    (hq u).mpr ⟨hP.2 i u hiu,fun v huv => hn.2 i v ((hGen i v).mpr ⟨u,hiu,huv⟩)⟩⟩
  exact ((hq x).mp (hx.2 Q hQ hOldQ hNewQ)).2 y hxy

theorem coefficients_image (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I W V G H unit e O P F old generators x y : M.Carrier .set}
    (hWhole : Submonoid W G unit W) (hO : MapsTo D W O) (hP : MapsTo I W P)
    (hF : Hom W V G H unit e F) (hOld : NodeMap O F old) (hGen : NodeMap P F generators)
    (hx : Coefficients w D I W G unit O P x) (hxy : PureKuratowski.PairMember M x y F) :
    Coefficients w D I V H e old generators y := by
  obtain ⟨S,hSD,hFin,hC⟩ := hx
  exact ⟨S,hSD,hFin,closure_image hM hWhole hO hP hF hOld hGen hC hxy⟩

/-- Literal Attachment.old, before constructing its composite old inclusion. -/
def OldFixed (O F : M.Carrier .set) : Prop := ∀ a x,
  PureKuratowski.PairMember M a x O → PureKuratowski.PairMember M x a F

def oldFixed {m : Nat} (O F : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ 1 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 0 1))))

theorem oldFixed_freeClosed {m : Nat} (O F : Fin m) : (oldFixed O F).FreeClosed := by
  simp [oldFixed,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem oldFixed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (O F : Fin m) :
    Project.Formula.satisfies env (oldFixed O F) ↔ OldFixed (env.bound O) (env.bound F) := by
  simp only [oldFixed,OldFixed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

/-- Actual range and the two actual composite graphs of the supplied map. -/
def ImageResult (w D I W V H e O P F R old generators : M.Carrier .set) : Prop :=
  Range W F R ∧ Subset R V ∧ Subset D R ∧ MapsTo D V old ∧ IdentityGraph D old ∧
    NodeMap O F old ∧ MapsTo I V generators ∧ NodeMap P F generators ∧
    ∀ y, (Project.FirstOrderSemantics.reduct M).mem y R → Coefficients w D I V H e old generators y

/-- Native range/composition constructors produce the actual attachment image
and its literal old inclusion. The proof does not assume a replacement image. -/
theorem exists_image (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I W V G H unit e O P F : M.Carrier .set}
    (hWhole : Submonoid W G unit W) (hO : MapsTo D W O) (hP : MapsTo I W P)
    (hF : Hom W V G H unit e F) (hFixed : OldFixed O F)
    (hCoefficients : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x W → Coefficients w D I W G unit O P x) :
    ∃ R old generators, ImageResult w D I W V H e O P F R old generators := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hNative := (ForcingSupportSize.native_mapsTo hM W V F).mp hF.1
  obtain ⟨R,hR⟩ := ZF.exists_range_of_setFunction hZF (KuratowskiZF.interpretation hM) hNative.1 hNative.2.1
  have hRange : Range W F R := fun y => ⟨fun hy => by
      obtain ⟨x,hxy⟩ := (hR y).mp hy
      exact ⟨x,function_input hF.1.1 hxy,hxy⟩,
    fun ⟨x,_,hxy⟩ => (hR y).mpr ⟨x,hxy⟩⟩
  obtain ⟨old,hOldMap,hOld⟩ := exists_node_map hM hO hF.1
  obtain ⟨generators,hGenMap,hGen⟩ := exists_node_map hM hP hF.1
  have hId : IdentityGraph D old := by
    intro a y
    constructor
    · intro hay
      obtain ⟨x,hax,hxy⟩ := (hOld a y).mp hay
      exact ⟨function_input hO.1 hax,(function_unique hF.1.1 hxy (hFixed a x hax)).symm⟩
    · rintro ⟨ha,rfl⟩
      obtain ⟨x,hax,_⟩ := hO.1.2 a ha
      exact (hOld a a).mpr ⟨x,hax,hFixed a x hax⟩
  refine ⟨R,old,generators,hRange,?_,?_,hOldMap,hId,hOld,hGenMap,hGen,?_⟩
  · intro y hy
    obtain ⟨x,_,hxy⟩ := (hRange y).mp hy
    exact hF.1.2 x y hxy
  · intro a ha
    obtain ⟨x,hax,hxa⟩ := (hOld a a).mp ((hId a a).mpr ⟨ha,rfl⟩)
    exact (hRange a).mpr ⟨x,hO.2 a x hax,hxa⟩
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := (hRange y).mp hy
    exact coefficients_image hM hWhole hO hP hF hOld hGen (hCoefficients x hx) hxy

/-- The precise closure-mono step in CellCuts.selected_word. The premise
says that THIS support is retained; a dependency-closed tower supplies it. -/
theorem retained_word {I V H e old generators coefficients D retained cut x : M.Carrier .set}
    (hId : IdentityGraph D old) (hCoeff : Subset coefficients D)
    (hCut : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a cut ↔
      (Project.FirstOrderSemantics.reduct M).mem a retained ∧ (Project.FirstOrderSemantics.reduct M).mem a D)
    (hRetained : ImageIn coefficients old retained)
    (hx : ClosureMember I V H e old generators coefficients x) :
    ClosureMember I V H e old generators cut x := by
  apply closure_mono (coefficients := coefficients) ?_ hx
  intro a ha
  have haD := hCoeff a ha
  exact (hCut a).mpr ⟨hRetained a a ha ((hId a a).mpr ⟨haD,rfl⟩),haD⟩

/-- Apply the same-support transfer to the actual Merger presentation. -/
theorem merger_image (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots V H eV F : M.Carrier .set}
    (hA : ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hF : Hom W V G H unit eV F) (hFixed : OldFixed O F) :
    ∃ R old generators, ImageResult w D n W V H eV O roots F R old generators := by
  have hWhole : Submonoid W G unit W := ⟨fun _ h => h,hA.unit_law.1,?_⟩
  · exact exists_image hM hWhole hA.old_hom.1 hA.roots_map hF hFixed
      (fun _ hx => ConstructionCellCoefficients.merger_coefficients hM hA hw hz hzw hx)
  · intro a b c _ _ hProd
    obtain ⟨pair,_,hpc⟩ := hProd
    exact hA.product_map.2 pair c hpc

/-- Apply the same-support transfer to the actual Probe presentation. -/
theorem probe_image (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F : M.Carrier .set}
    (hA : ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hF : Hom W V G H unit eV F) (hFixed : OldFixed O F) :
    ∃ R old generators, ImageResult w D w W V H eV O P F R old generators := by
  have hm := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication
  have hWhole : Submonoid W G unit W := ⟨fun _ h => h,hm.1.1,
    fun _ _ _ ha hb hProd => ConstructionMergerRelations.product_range hm ha hb hProd⟩
  exact exists_image hM hWhole hA.old_map hA.probes_map hF hFixed
    (fun _ hx => ConstructionCellCoefficients.probe_coefficients hM hA hw hz hzw hx)

def imageResult {m : Nat} (w D I W V H e O P F R old generators : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingSupportedNames.range W F R))
    (.conj (Project.Formula.subset (.bound R) (.bound V))
      (.conj (Project.Formula.subset (.bound D) (.bound R))
        (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo old D V))
          (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D old))
            (.conj (ConstructionProbeMappedPathSyntax.nodeMap O F old)
              (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo generators I V))
                (.conj (ConstructionProbeMappedPathSyntax.nodeMap P F generators)
                  (.forallE (.imp (.mem (.bound 0) (.bound R.succ))
                    (ConstructionCellCoefficients.coefficients w.succ D.succ I.succ V.succ H.succ e.succ old.succ generators.succ 0))))))))))

theorem imageResult_freeClosed {m : Nat} (w D I W V H e O P F R old generators : Fin m) :
    (imageResult w D I W V H e O P F R old generators).FreeClosed := by
  simp [imageResult,Definitional.Formula.FreeClosed,Project.Formula.subset,
    ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
    ConstructionCellCoefficients.coefficients_freeClosed]

theorem imageResult_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I W V H e O P F R old generators : Fin m) :
    Project.Formula.satisfies env (imageResult w D I W V H e O P F R old generators) ↔
      ImageResult (env.bound w) (env.bound D) (env.bound I) (env.bound W) (env.bound V) (env.bound H) (env.bound e)
        (env.bound O) (env.bound P) (env.bound F) (env.bound R) (env.bound old) (env.bound generators) := by
  simp only [imageResult,ImageResult,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionCellCoefficients.coefficients_semantics hM]
  rfl

/-- Identify the constructed range with the SAME named attachment endpoint. -/
theorem image_at_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I W V H e O P F R R' old generators : M.Carrier .set}
    (hResult : ImageResult w D I W V H e O P F R' old generators) (hRange : Range W F R) :
    ImageResult w D I W V H e O P F R old generators := by
  have he : R' = R := (ModelTransfer.extensionality hM).eq_of_same_members R' R
    (fun x => (hResult.1 x).trans (hRange x).symm)
  exact he ▸ hResult

/-- The supplied actual attachment endpoint R is preserved. Only its
composite old/generator graphs are existentially constructed. -/
def mergerSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots)
        (.imp (ConstructionProbePushoutSyntax.hom W V G H unit eV F) (.imp (oldFixed O F)
          (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W F R))
            (.existsE (.existsE (imageResult w.succ.succ D.succ.succ n.succ.succ W.succ.succ V.succ.succ H.succ.succ eV.succ.succ O.succ.succ roots.succ.succ F.succ.succ R.succ.succ 1 0))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isSuccessor,Project.Formula.isEmpty,ConstructionMergerPushout.presentation_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,oldFixed_freeClosed,imageResult_freeClosed,ProjectSyntax.freeClosed]

theorem merger_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,ConstructionMergerPushout.presentation_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,oldFixed_semantics hM,imageResult_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportedNames.range_semantics (M := M)]
  intro hw hz hzw hA hF hFixed hRange
  obtain ⟨R',old,generators,hResult⟩ := merger_image hM hA hw hz hzw hF hFixed
  exact ⟨old,generators,image_at_range hM hResult hRange⟩

theorem merger_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)) :=
  ModelTransfer.derives (fun _ hM => merger_models w n zero D mul e P C L projection A W T B G unit O roots V H eV F R hM)

/-- The supplied actual attachment endpoint R is preserved. Only its
composite old/generator graphs are existentially constructed. -/
def probeSentence {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionProbePushoutSyntax.presentation w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
        (.imp (ConstructionProbePushoutSyntax.hom W V G H unit eV F) (.imp (oldFixed O F)
          (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W F R))
            (.existsE (.existsE (imageResult w.succ.succ D.succ.succ w.succ.succ W.succ.succ V.succ.succ H.succ.succ eV.succ.succ O.succ.succ P.succ.succ F.succ.succ R.succ.succ 1 0))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isSuccessor,Project.Formula.isEmpty,ConstructionProbePushoutSyntax.presentation_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,oldFixed_freeClosed,imageResult_freeClosed,ProjectSyntax.freeClosed]

theorem probe_models {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,ConstructionProbePushoutSyntax.presentation_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,oldFixed_semantics hM,imageResult_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportedNames.range_semantics (M := M)]
  intro hw hz hzw hA hF hFixed hRange
  obtain ⟨R',old,generators,hResult⟩ := probe_image hM hA hw hz hzw hF hFixed
  exact ⟨old,generators,image_at_range hM hResult hRange⟩

theorem probe_kernel_certificate {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)) :=
  ModelTransfer.derives (fun _ hM => probe_models w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R hM)

/-- The same actual retained cut used by the source selected construction. -/
def intersection {m : Nat} (cut retained D : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound cut.succ))
    (.conj (.mem (.bound 0) (.bound retained.succ)) (.mem (.bound 0) (.bound D.succ))))

theorem intersection_freeClosed {m : Nat} (cut retained D : Fin m) :
    (intersection cut retained D).FreeClosed := by
  simp [intersection,Definitional.Formula.FreeClosed]

theorem intersection_semantics {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (cut retained D : Fin m) :
    Project.Formula.satisfies env (intersection cut retained D) ↔
      ∀ a, (Project.FirstOrderSemantics.reduct M).mem a (env.bound cut) ↔
        (Project.FirstOrderSemantics.reduct M).mem a (env.bound retained) ∧
          (Project.FirstOrderSemantics.reduct M).mem a (env.bound D) := by
  simp only [intersection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
  rfl

theorem exists_retained_cut (hM : FirstOrder.Theory.Models M nativeZF)
    {I V H e old generators coefficients D retained x : M.Carrier .set}
    (hId : IdentityGraph D old) (hCoeff : Subset coefficients D)
    (hRetained : ImageIn coefficients old retained)
    (hx : ClosureMember I V H e old generators coefficients x) :
    ∃ cut, (∀ a, (Project.FirstOrderSemantics.reduct M).mem a cut ↔
      (Project.FirstOrderSemantics.reduct M).mem a retained ∧ (Project.FirstOrderSemantics.reduct M).mem a D) ∧
      ClosureMember I V H e old generators cut x := by
  obtain ⟨cut,hCut⟩ := KP.intersection_exists_d (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) retained D
  exact ⟨cut,hCut,retained_word hId hCoeff hCut hRetained hx⟩

/-- The local selected_word inference, with retained-support containment
explicit. This does not assume that the actual tower dependency graph exists. -/
def retainedSentence {m : Nat} (I V H e old generators coefficients D retained x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D old))
      (.imp (Project.Formula.subset (.bound coefficients) (.bound D))
        (.imp (imageIn coefficients old retained)
          (.imp (closureMember I V H e old generators coefficients x)
            (.existsE (.conj (intersection 0 retained.succ D.succ)
              (closureMember I.succ V.succ H.succ e.succ old.succ generators.succ 0 x.succ)))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,
      imageIn_freeClosed,closureMember_freeClosed,intersection_freeClosed]

theorem retained_models {m : Nat} (I V H e old generators coefficients D retained x : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (retainedSentence I V H e old generators coefficients D retained x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (retainedSentence I V H e old generators coefficients D retained x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),imageIn_semantics hM,
    closureMember_semantics hM,intersection_semantics (M := M)]
  exact exists_retained_cut hM

theorem retained_kernel_certificate {m : Nat} (I V H e old generators coefficients D retained x : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (retainedSentence I V H e old generators coefficients D retained x)) :=
  ModelTransfer.derives (fun _ hM => retained_models I V H e old generators coefficients D retained x hM)

end PPAC.Migration.ConstructionAttachmentCoefficients
