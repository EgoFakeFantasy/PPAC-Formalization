/- Pinned ConservativeCells.Probe.generated / Merger.generated.
Restrict the actual multiplication with native ZF.exists_restriction, then
reuse the actual presentedLift and presentedHom_ext, exactly as in the source.
This is an ordinary submonoid: no factor/join closure is silently required. -/
import PPAC.Migration.ConstructionMergerWordTransport
import PPAC.Migration.ConstructionConservativeHull

namespace PPAC.Migration.ConstructionCellGeneration
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionConservativeHull (MulClosed ProductGraph)
open ConstructionRealCuts (Subset)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_indices)
open ConstructionProbeHomEvaluation (product_unique)
open ConstructionProbePushout (Hom)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (Unit Associative)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Submonoid (W G unit S : M.Carrier .set) : Prop :=
  Subset S W ∧ (Project.FirstOrderSemantics.reduct M).mem unit S ∧ MulClosed S G

/-- Minimal adaptation of the existing conservative-hull product restriction:
only product closure is used, with ambient total/functional product graphs. -/
theorem exists_product (hM : FirstOrder.Theory.Models M nativeZF)
    {W G unit S : M.Carrier .set}
    (hTotal : ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x W → (Project.FirstOrderSemantics.reduct M).mem y W →
      ∃ z, (Project.FirstOrderSemantics.reduct M).mem z W ∧ Product G x y z)
    (hUnique : ∀ x y z t, (Project.FirstOrderSemantics.reduct M).mem x W → (Project.FirstOrderSemantics.reduct M).mem y W →
      Product G x y z → Product G x y t → z = t)
    (hS : Submonoid W G unit S) :
    ∃ BS GS, Representatives S S BS ∧ MapsTo BS S GS ∧ ProductGraph S G GS := by
  obtain ⟨BS,hBS⟩ := ConstructionProbeLetters.exists_representatives hM S S
  obtain ⟨GS,hR⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) G BS
  have hGraph : ProductGraph S G GS := by
    intro x y z
    constructor
    · rintro ⟨p,hcode,hpz⟩
      obtain ⟨hpB,hpm⟩ := (hR.2 p z).mp hpz
      obtain ⟨x',y',hx,hy,hcode'⟩ := (hBS p).mp hpB
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact ⟨hx,hy,p,hcode,hpm⟩
    · rintro ⟨hx,hy,p,hcode,hpz⟩
      exact ⟨p,hcode,(hR.2 p z).mpr ⟨(hBS p).mpr ⟨x,y,hx,hy,hcode⟩,hpz⟩⟩
  refine ⟨BS,GS,hBS,⟨⟨?_,?_⟩,?_⟩,hGraph⟩
  · intro row hrow
    obtain ⟨p,z,hcode⟩ := hR.1 row hrow
    exact ⟨p,z,((hR.2 p z).mp ⟨row,hcode,hrow⟩).1,hcode⟩
  · intro p hp
    obtain ⟨x,y,hx,hy,hcode⟩ := (hBS p).mp hp
    obtain ⟨z,_,hpz⟩ := hTotal x y (hS.1 x hx) (hS.1 y hy)
    obtain ⟨p',hcode',hp'z⟩ := (hGraph x y z).mpr ⟨hx,hy,hpz⟩
    have he : p' = p := KuratowskiZF.code_unique hM hcode' hcode
    subst p'
    exact ⟨z,hp'z,fun t hpt => hUnique x y t z (hS.1 x hx) (hS.1 y hy) ((hGraph x y t).mp ⟨p,hcode,hpt⟩).2.2 hpz⟩
  · intro p z hpz
    obtain ⟨hp,_⟩ := (hR.2 p z).mp hpz
    obtain ⟨x,y,hx,hy,hcode⟩ := (hBS p).mp hp
    exact hS.2.2 x y z hx hy ((hGraph x y z).mp ⟨p,hcode,hpz⟩).2.2

theorem unit_restrict {W G unit S GS : M.Carrier .set}
    (hU : Unit W G unit) (hS : Submonoid W G unit S) (hGS : ProductGraph S G GS) : Unit S GS unit := by
  refine ⟨hS.2.1,?_⟩
  intro x hx y
  exact ⟨⟨fun h => (hU.2 x (hS.1 x hx) y).1.mp ((hGS unit x y).mp h).2.2,
    fun h => (hGS unit x y).mpr ⟨hS.2.1,hx,(hU.2 x (hS.1 x hx) y).1.mpr h⟩⟩,
    ⟨fun h => (hU.2 x (hS.1 x hx) y).2.mp ((hGS x unit y).mp h).2.2,
    fun h => (hGS x unit y).mpr ⟨hx,hS.2.1,(hU.2 x (hS.1 x hx) y).2.mpr h⟩⟩⟩

theorem associative_restrict {W G unit S GS : M.Carrier .set}
    (hAssoc : Associative W G) (hS : Submonoid W G unit S) (hGS : ProductGraph S G GS) : Associative S GS := by
  intro a b c ab bc z ha hb hc hab hbc
  have hab' := ((hGS a b ab).mp hab).2.2
  have hbc' := ((hGS b c bc).mp hbc).2.2
  have habS := hS.2.2 a b ab ha hb hab'
  have hbcS := hS.2.2 b c bc hb hc hbc'
  exact ⟨fun h => (hGS a bc z).mpr ⟨ha,hbcS,
      (hAssoc a b c ab bc z (hS.1 a ha) (hS.1 b hb) (hS.1 c hc) hab' hbc').mp ((hGS ab c z).mp h).2.2⟩,
    fun h => (hGS ab c z).mpr ⟨habS,hc,
      (hAssoc a b c ab bc z (hS.1 a ha) (hS.1 b hb) (hS.1 c hc) hab' hbc').mpr ((hGS a bc z).mp h).2.2⟩⟩

theorem hom_restrict {D W mul G e unit S GS F : M.Carrier .set}
    (hf : Hom D W mul G e unit F) (hRange : MapsTo D S F) (hGS : ProductGraph S G GS) : Hom D S mul GS e unit F := by
  refine ⟨hRange,hf.2.1,?_⟩
  intro x y z fx fy fz hp hx hy hz
  exact (hGS fx fy fz).mpr ⟨hRange.2 x fx hx,hRange.2 y fy hy,hf.2.2 x y z fx fy fz hp hx hy hz⟩

theorem hom_include {D W mul G e unit S GS F : M.Carrier .set}
    (hf : Hom D S mul GS e unit F) (hS : Subset S W) (hGS : ProductGraph S G GS) : Hom D W mul G e unit F := by
  refine ⟨⟨hf.1.1,fun x y h => hS y (hf.1.2 x y h)⟩,hf.2.1,?_⟩
  intro x y z fx fy fz hp hx hy hz
  exact ((hGS fx fy fz).mp (hf.2.2 x y z fx fy fz hp hx hy hz)).2.2

/-- Literal source generated: every internal submonoid containing both full
generator images equals the actual whole extension. -/
def Generated (D I W G unit O P : M.Carrier .set) : Prop := ∀ S,
  Submonoid W G unit S → MapsTo D S O → MapsTo I S P → S = W

theorem merger_generated (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots : M.Carrier .set}
    (hA : ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) : Generated D n W G unit O roots := by
  intro S hS ho hn
  obtain ⟨BS,GS,hBS,hGS,hGraph⟩ := exists_product hM
    (fun _ _ hx hy => projected hM hA.product_representatives hA.product_map hx hy)
    (fun _ _ _ _ _ _ hp hq => product_unique hM hA.product_map hp hq) hS
  have hU := unit_restrict hA.unit_law hS hGraph
  have hAssoc := associative_restrict hA.associative hS hGraph
  have hOld := hom_restrict hA.old_hom ho hGraph
  have hSat := ConstructionMergerPushout.roots_satisfy hM hA hw hz
  have hSatS : ConstructionMergerPresentedLift.Satisfies P O roots GS := by
    intro i j a b u v hij hab hu hv
    obtain ⟨pi,fa,hpi,hfa,hpu⟩ := hu
    obtain ⟨pj,fb,hpj,hfb,hpv⟩ := hv
    exact hSat i j a b u v hij hab ⟨pi,fa,hpi,hfa,((hGraph pi fa u).mp hpu).2.2⟩
      ⟨pj,fb,hpj,hfb,((hGraph pj fb v).mp hpv).2.2⟩
  obtain ⟨F,hF,hFO,hFR,_⟩ := ConstructionMergerPushout.presentation_lift hM hA hw hz hzw hBS hGS hU hAssoc hOld hn hSatS
  have hFW := hom_include hF hS.1 hGraph
  obtain ⟨ident,hId,hIdentity⟩ := ConstructionPushoutIdentification.exists_hom_identity hM hA.unit_law.1
  have he := ConstructionMergerPushout.presentation_ext hM hA hw hz hzw hA.product_representatives
    hA.product_map hA.unit_law hA.associative hFW hId hA.old_hom hA.roots_map hFO hFR
    (ConstructionPushoutIdentification.right_identity hA.old_hom.1 hIdentity)
    (ConstructionPushoutIdentification.right_identity hA.roots_map hIdentity)
  apply (ModelTransfer.extensionality hM).eq_of_same_members S W
  intro x
  constructor
  · exact hS.1 x
  · intro hx
    have hFx : PureKuratowski.PairMember M x x F := he ▸ (hIdentity x x).mpr ⟨hx,rfl⟩
    exact hF.1.2 x x hFx


/-- Source Probe.generated, using the actual adjacent/exit relations to lift
into the arbitrary submonoid, then the already proved presentedHom_ext. -/
theorem probe_generated (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : M.Carrier .set}
    (hA : ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) : Generated D w W G unit O P := by
  intro S hS ho hn
  have hm := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication
  have hTotal x y hx hy := (hm.2.1 x hx).1 y hy
  have hUnique x y z t hx hy hp hq := (hm.2.1 x hx).2.1 y z t hy hp hq
  obtain ⟨BS,GS,hBS,hGS,hGraph⟩ := exists_product hM hTotal hUnique hS
  have hU := unit_restrict hm.1 hS hGraph
  have hAssoc := associative_restrict hm.2.2 hS hGraph
  have hEmb := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem
    hA.old_unit hA.multiplication hA.old_graph
  have hOldW : Hom D W mul G e unit O := ⟨hA.old_map,hEmb.1,fun x y z ox oy oz hp hx hy hzv => hEmb.2.1 x y z ox oy oz hx hy hzv hp⟩
  have hOld := hom_restrict hOldW ho hGraph
  have hRel := ConstructionProbePushout.presentation_relations hA hw hz hzw
  have hAdj : ConstructionProbePresentationTransitions.Adjacent w factor O P GS := by
    intro i j _ _ _ r oldr pi pj hr hor hpi hpj
    exact (hGraph oldr pj pi).mpr ⟨ho.2 r oldr hor,hn.2 j pj hpj,
      hRel.2 i j r pi pj oldr hr hpi hpj ((hA.old_graph r oldr).mp hor)⟩
  have hExit : ConstructionProbePresentedLift.IndexedExit terminal mul d b O P GS := by
    intro i t z pi ob oz ht hp hpi hob hoz
    exact (hGraph pi ob oz).mpr ⟨hn.2 i pi hpi,ho.2 b ob hob,
      hRel.1 i pi t z ob oz hpi ht hp ((hA.old_graph b ob).mp hob) ((hA.old_graph z oz).mp hoz)⟩
  obtain ⟨F,hF,hLaw⟩ := ConstructionProbePushout.presentation_lift hA hw hz hzw hBS hGS hOld hn hU hAssoc hAdj hExit
  have hFW := hom_include hF hS.1 hGraph
  -- The presentation records product values. Use its canonical whole-carrier
  -- restriction for the target function graph required by presentedHom_ext.
  have hWhole : Submonoid W G unit W := ⟨fun _ h => h,hm.1.1,
    fun x y z hx hy hp => ConstructionMergerRelations.product_range hm hx hy hp⟩
  obtain ⟨BW,GW,_,hGW,hGraphW⟩ := exists_product hM hTotal hUnique hWhole
  have hFWhole := hom_restrict hFW hFW.1 hGraphW
  obtain ⟨ident,hId,hIdentity⟩ := ConstructionPushoutIdentification.exists_hom_identity hM hm.1.1
  have hIdWhole := hom_restrict hId hId.1 hGraphW
  have he : F = ident := ConstructionProbePushout.presentation_ext hA hw hz hzw hGW hFWhole.1 hIdWhole.1 hFWhole.2.2 hIdWhole.2.2 (by
    intro x q hOld y z hy hzv
    have hOldY := (hA.old_graph x y).mp ((hLaw.1.2.2 x q y hOld).mp hy)
    exact (ConstructionProbeRaw.old_unique hM hOldY hOld).trans ((hIdentity q z).mp hzv).2) (by
    intro i q hNew y z hy hzv
    have hNewY := (hLaw.2 i q y hNew).mp hy
    exact (ForcingConditionGraphs.function_unique hA.probes_map.1 hNewY hNew).trans ((hIdentity q z).mp hzv).2)
  apply (ModelTransfer.extensionality hM).eq_of_same_members S W
  intro x
  constructor
  · exact hS.1 x
  · intro hx
    have hFx : PureKuratowski.PairMember M x x F := he ▸ (hIdentity x x).mpr ⟨hx,rfl⟩
    exact hF.1.2 x x hFx

/-- Pure membership formula for the ordinary internal submonoid. -/
def submonoid {m : Nat} (W G unit S : Fin m) : Project.Formula 1 m :=
  .conj (.forallE (.imp (.mem (.bound 0) (.bound S.succ))
    (.mem (.bound 0) (.bound W.succ))))
    (.conj (.mem (.bound unit) (.bound S)) (ConstructionConservativeHull.mulClosed S G))

theorem submonoid_freeClosed {m : Nat} (W G unit S : Fin m) :
    (submonoid W G unit S).FreeClosed := by
  simp [submonoid,Definitional.Formula.FreeClosed,ConstructionConservativeHull.mulClosed_freeClosed]

theorem submonoid_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W G unit S : Fin m) :
    Project.Formula.satisfies env (submonoid W G unit S) ↔
      Submonoid (env.bound W) (env.bound G) (env.bound unit) (env.bound S) := by
  simp only [submonoid,Submonoid,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionConservativeHull.mulClosed_semantics hM]
  rfl

def generated {m : Nat} (D I W G unit O P : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (submonoid W.succ G.succ unit.succ 0)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O.succ D.succ 0))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo P.succ I.succ 0))
        (Project.Formula.extensionalEq (.bound 0) (.bound W.succ)))))

theorem generated_freeClosed {m : Nat} (D I W G unit O P : Fin m) :
    (generated D I W G unit O P).FreeClosed := by
  simp [generated,Definitional.Formula.FreeClosed,submonoid_freeClosed,
    ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem generated_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I W G unit O P : Fin m) :
    Project.Formula.satisfies env (generated D I W G unit O P) ↔
      Generated (env.bound D) (env.bound I) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound P) := by
  simp only [generated,Generated,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    submonoid_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

/-- Containment of the image of the selected old coefficients. -/
def ImageIn (coefficients O S : M.Carrier .set) : Prop := ∀ a x,
  (Project.FirstOrderSemantics.reduct M).mem a coefficients →
  PureKuratowski.PairMember M a x O → (Project.FirstOrderSemantics.reduct M).mem x S

/-- Membership in the ordinary generated submonoid, with the entire new
family retained. The quantified submonoids are internal sets. -/
def ClosureMember (I W G unit O P coefficients x : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem x W ∧ ∀ S,
    Submonoid W G unit S → ImageIn coefficients O S → MapsTo I S P →
      (Project.FirstOrderSemantics.reduct M).mem x S

def imageIn {m : Nat} (coefficients O S : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound coefficients.succ.succ))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ 1 0))
      (.mem (.bound 0) (.bound S.succ.succ)))))

theorem imageIn_freeClosed {m : Nat} (coefficients O S : Fin m) :
    (imageIn coefficients O S).FreeClosed := by
  simp [imageIn,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem imageIn_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (coefficients O S : Fin m) :
    Project.Formula.satisfies env (imageIn coefficients O S) ↔
      ImageIn (env.bound coefficients) (env.bound O) (env.bound S) := by
  simp only [imageIn,ImageIn,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def closureMember {m : Nat} (I W G unit O P coefficients x : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound x) (.bound W))
    (.forallE (.imp (submonoid W.succ G.succ unit.succ 0)
      (.imp (imageIn coefficients.succ O.succ 0)
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo P.succ I.succ 0))
          (.mem (.bound x.succ) (.bound 0))))))

theorem closureMember_freeClosed {m : Nat} (I W G unit O P coefficients x : Fin m) :
    (closureMember I W G unit O P coefficients x).FreeClosed := by
  simp [closureMember,Definitional.Formula.FreeClosed,submonoid_freeClosed,imageIn_freeClosed,ProjectSyntax.freeClosed]

theorem closureMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I W G unit O P coefficients x : Fin m) :
    Project.Formula.satisfies env (closureMember I W G unit O P coefficients x) ↔
      ClosureMember (env.bound I) (env.bound W) (env.bound G) (env.bound unit)
        (env.bound O) (env.bound P) (env.bound coefficients) (env.bound x) := by
  simp only [closureMember,ClosureMember,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    submonoid_semantics hM,imageIn_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

/-- Native Separation constructs the actual least submonoid. Thus
ClosureMember is not an assumed or external closure operation. -/
theorem exists_closure (hM : FirstOrder.Theory.Models M nativeZF)
    {D I W G unit O P : M.Carrier .set} (coefficients : M.Carrier .set)
    (hWhole : Submonoid W G unit W) (hO : MapsTo D W O) (hP : MapsTo I W P) :
    ∃ C, Submonoid W G unit C ∧ ImageIn coefficients O C ∧ MapsTo I C P ∧
      (∀ x, (Project.FirstOrderSemantics.reduct M).mem x C ↔ ClosureMember I W G unit O P coefficients x) ∧
      ∀ S, Submonoid W G unit S → ImageIn coefficients O S → MapsTo I S P → Subset C S := by
  let schema : Project.UnarySchema 7 := {
    body := closureMember 1 2 3 4 5 6 7 0
    freeClosed := closureMember_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases I (Fin.cases W (Fin.cases G (Fin.cases unit (Fin.cases O (Fin.cases P (fun _ => coefficients))))))
    free := fun _ => W }
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env W
  have hc x : (Project.FirstOrderSemantics.reduct M).mem x C ↔ ClosureMember I W G unit O P coefficients x := by
    have he : schema.denote env x ↔ ClosureMember I W G unit O P coefficients x :=
      closureMember_semantics hM (env.push x) 1 2 3 4 5 6 7 0
    exact (hC x).trans ⟨fun h => he.mp h.2,fun h => ⟨h.1,he.mpr h⟩⟩
  refine ⟨C,⟨fun x hx => ((hc x).mp hx).1,?_,?_⟩,?_,⟨hP.1,?_⟩,hc,?_⟩
  · exact (hc unit).mpr ⟨hWhole.2.1,fun _ hs _ _ => hs.2.1⟩
  · intro x y z hx hy hp
    obtain ⟨hxW,hx⟩ := (hc x).mp hx
    obtain ⟨hyW,hy⟩ := (hc y).mp hy
    exact (hc z).mpr ⟨hWhole.2.2 x y z hxW hyW hp,
      fun S hs ho hn => hs.2.2 x y z (hx S hs ho hn) (hy S hs ho hn) hp⟩
  · intro a x ha hax
    exact (hc x).mpr ⟨hO.2 a x hax,fun _ _ ho _ => ho a x ha hax⟩
  · intro i x hix
    exact (hc x).mpr ⟨hP.2 i x hix,fun _ _ _ hn => hn.2 i x hix⟩
  · intro S hs ho hn x hx
    exact ((hc x).mp hx).2 S hs ho hn

/-- Pinned Cell.mem_closure, obtained from the two proved generated theorems. -/
theorem mem_closure {D I W G unit O P x : M.Carrier .set}
    (hGen : Generated D I W G unit O P) (hO : MapsTo D W O)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) : ClosureMember I W G unit O P D x := by
  refine ⟨hx,fun S hs ho hn => ?_⟩
  have hMap : MapsTo D S O := ⟨hO.1,fun a y hay =>
    ho a y (ForcingConditionGraphs.function_input hO.1 hay) hay⟩
  exact (hGen S hs hMap hn).symm ▸ hx

/-- Monotonicity used by the two finite-coefficient union branches. -/
theorem closure_mono {I W G unit O P coefficients larger x : M.Carrier .set}
    (hSubset : Subset coefficients larger) (hx : ClosureMember I W G unit O P coefficients x) :
    ClosureMember I W G unit O P larger x :=
  ⟨hx.1,fun S hs ho hn => hx.2 S hs (fun a y ha hay => ho a y (hSubset a ha) hay) hn⟩

/-- All presentations and all internal submonoids are quantified in native ZF. -/
def mergerSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots)
        (.conj (generated D n W G unit O roots)
          (.forallE (.imp (.mem (.bound 0) (.bound W.succ))
            (closureMember n.succ W.succ G.succ unit.succ O.succ roots.succ D.succ 0))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,Project.Formula.isSuccessor,Project.Formula.isEmpty,
      ConstructionMergerPushout.presentation_freeClosed,generated_freeClosed,closureMember_freeClosed]

theorem merger_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionMergerPushout.presentation_semantics hM,generated_semantics hM,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,closureMember_semantics hM]
  intro hw hz hzw hA
  have hg := merger_generated hM hA hw hz hzw
  exact ⟨hg,fun _ hx => mem_closure hg hA.old_hom.1 hx⟩

theorem merger_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots)) :=
  ModelTransfer.derives (fun _ hM => merger_models w n zero D mul e P C L projection A W T B G unit O roots hM)

/-- All presentations and all internal submonoids are quantified in native ZF. -/
def probeSentence {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionProbePushoutSyntax.presentation w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
        (.conj (generated D w W G unit O P)
          (.forallE (.imp (.mem (.bound 0) (.bound W.succ))
            (closureMember w.succ W.succ G.succ unit.succ O.succ P.succ D.succ 0))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,Project.Formula.isSuccessor,Project.Formula.isEmpty,
      ConstructionProbePushoutSyntax.presentation_freeClosed,generated_freeClosed,closureMember_freeClosed]

theorem probe_models {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionProbePushoutSyntax.presentation_semantics hM,generated_semantics hM,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,closureMember_semantics hM]
  intro hw hz hzw hA
  have hg := probe_generated hM hA hw hz hzw
  exact ⟨hg,fun _ hx => mem_closure hg hA.old_map hx⟩

theorem probe_kernel_certificate {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)) :=
  ModelTransfer.derives (fun _ hM => probe_models w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O hM)

/-- Existence of the actual internal closure, from ordinary ZF only. -/
def closureSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (submonoid 2 3 4 2)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 5 0 2))
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 6 1 2))
          (.existsE (.conj (submonoid 3 4 5 0) (.conj (imageIn 8 6 0)
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 7 2 0))
              (.forallE (.iff (.mem (.bound 0) (.bound 1))
                (closureMember 3 4 5 6 7 8 9 0))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,submonoid_freeClosed,imageIn_freeClosed,
      closureMember_freeClosed,ProjectSyntax.freeClosed]

theorem closure_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence closureSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) closureSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    submonoid_semantics hM,imageIn_semantics hM,closureMember_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M)]
  intro hWhole hO hP
  obtain ⟨C,hC,ho,hp,hc,_⟩ := exists_closure hM (bound 7) hWhole hO hP
  exact ⟨C,hC,ho,hp,hc⟩

theorem closure_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence closureSentence) :=
  ModelTransfer.derives (fun _ hM => closure_models hM)

end PPAC.Migration.ConstructionCellGeneration
