/- Pinned Diagrams.amalgamate:217/common_extension:245.
Use SAME literal prescription and actual roots; glue their right-cone labels
and extend the resulting INTERNAL partial injection to the WHOLE carrier.
All graph, cardinal, Choice and permutation backends are existing. -/
import PPAC.Migration.ConstructionDiagramPrescription

namespace PPAC.Migration.ConstructionDiagramAmalgamation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection MapsTo Small)
open ForcingDiagramOrder (Product Sub)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionDiagramPrescription (Family ExactFamily Matches)
open ConstructionSaturationMergers (Realization)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem whole_embedding (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mu : M.Carrier .set}
    (hMu : (Project.FirstOrderSemantics.reduct M).IsCardinal (KuratowskiZF.interpretation hM) mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small D mu) : ∃ e, Injection D I e := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF pair mu
  have hMuI := (hI.2 mu hMu.1).mpr ⟨id,hId.1⟩
  obtain ⟨incl,hIncl⟩ := ZF.exists_inclusionInjection hZF pair (hI.1.transitive.memberSubset hMuI)
  obtain ⟨f,hf⟩ := (ForcingSupportSize.native_small hM D mu).mp hD
  obtain ⟨e,he⟩ := ZF.exists_compositionInjection hZF pair hf hIncl
  exact ⟨e,(ForcingSupportSize.native_injection hM D I e).mpr he⟩

theorem restrict_injection (hM : FirstOrder.Theory.Models M nativeZF)
    {D I U e : M.Carrier .set}
    (he : Injection D I e)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset U D) :
    ∃ s, Injection U I s ∧ ∀ x y, PureKuratowski.PairMember M x y s ↔
      (Project.FirstOrderSemantics.reduct M).mem x U ∧ PureKuratowski.PairMember M x y e := by
  obtain ⟨s,hR⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) e U
  refine ⟨s,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,hR.2⟩
  · intro row hrow
    obtain ⟨x,y,hCode⟩ := hR.1 row hrow
    exact ⟨x,y,((hR.2 x y).mp ⟨row,hCode,hrow⟩).1,hCode⟩
  · intro x hx
    obtain ⟨y,hxy,_⟩ := he.1.1.2 x (hSub x hx)
    exact ⟨y,(hR.2 x y).mpr ⟨hx,hxy⟩,
      fun z hz => ForcingConditionGraphs.function_unique he.1.1 ((hR.2 x z).mp hz).2 hxy⟩
  · intro x y hxy
    exact he.1.2 x y ((hR.2 x y).mp hxy).2
  · intro x y z hx hy
    exact he.2 x y z ((hR.2 x z).mp hx).2 ((hR.2 y z).mp hy).2

/-- Original extend_embedding, at the ACTUAL infinite-budget parameters.
Move through the EXISTING between_diagrams adapter instead of rebuilding
inverse/range/composition graphs for a second time. -/
theorem extend_embedding (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu D I U e f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu) (hD : Small D mu)
    (he : Injection D I e) (hf : Injection U I f)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset U D) :
    ∃ r, Injection D I r ∧ ConstructionPlacementExtensions.Extends f r := by
  obtain ⟨s,hs,hRestr⟩ := restrict_injection hM he hSub
  have hSmallU := ForcingSupportSize.small_subset hM hSub hD
  obtain ⟨S,g,hSI,hSize,hg,hMatch⟩ := ConstructionDiagramPlacements.between_diagrams hM hs hf hSmallU
  obtain ⟨pi,hpi,hExt⟩ := ConstructionPlacementExtensions.extend_permutation hM hChoice hw hMu hLarge hSI hSize hg
  obtain ⟨r,hr,hComp⟩ := ForcingDiagramAction.exists_permute hM hpi he
  refine ⟨r,hr,?_⟩
  intro x z hxz
  have hxU := ForcingConditionGraphs.function_input hf.1.1 hxz
  obtain ⟨y,hxy,_⟩ := he.1.1.2 x (hSub x hxU)
  have hsxy := (hRestr x y).mpr ⟨hxU,hxy⟩
  exact (hComp x z).mpr ⟨hSub x hxU,y,hxy,hExt y z (hMatch x y z hsxy hxz)⟩

def Glue (n D mul F roots m label : M.Carrier .set) : Prop :=
  ∃ i x r ri, (Project.FirstOrderSemantics.reduct M).mem i n ∧
    (Project.FirstOrderSemantics.reduct M).mem x D ∧
    PureKuratowski.PairMember M i r F ∧ PureKuratowski.PairMember M i ri roots ∧
    Product mul ri x m ∧ PureKuratowski.PairMember M x label r

def Subdiagrams (n D mul F roots r : M.Carrier .set) : Prop :=
  ∀ i s ri, (Project.FirstOrderSemantics.reduct M).mem i n →
    PureKuratowski.PairMember M i s F → PureKuratowski.PairMember M i ri roots → Sub D mul r ri s

def CommonExtension (n D I mul F r : M.Carrier .set) : Prop :=
  Injection D I r ∧ ∀ i s, (Project.FirstOrderSemantics.reduct M).mem i n →
    PureKuratowski.PairMember M i s F → ForcingDiagramOrder.Le D mul r s

def Result (n D I mul F P identity roots r : M.Carrier .set) : Prop :=
  ConstructionDiagramPrescription.Result n D mul F P ∧
    MapsTo D D identity ∧ ForcingConditionGraphs.IdentityGraph D identity ∧ MapsTo n D roots ∧
    ConstructionMergerRootSystem.RootSystem n P D mul identity roots ∧ Realization n D mul P roots ∧
    Subdiagrams n D mul F roots r ∧ CommonExtension n D I mul F r

theorem glue_functional {n D I mul F P roots m a b : M.Carrier .set}
    (hF : Family n D I F) (hMatch : Matches n D mul F P) (hReal : Realization n D mul P roots)
    (hA : Glue n D mul F roots m a) (hB : Glue n D mul F roots m b) : a = b := by
  obtain ⟨i,x,r,ri,hi,hx,hri,hRootI,hProductI,hrxa⟩ := hA
  obtain ⟨j,y,s,rj,hj,hy,hsj,hRootJ,hProductJ,hsyb⟩ := hB
  have hRel := (hReal i j x y ri rj m m hi hj hx hy hRootI hRootJ hProductI hProductJ).mp rfl
  obtain ⟨z,hrxz,hsyz⟩ := (hMatch i x j y r s hi hx hj hy hri hsj).mpr hRel
  exact (ForcingConditionGraphs.function_unique (hF.2 i r hri).1.1 hrxa hrxz).trans
    (ForcingConditionGraphs.function_unique (hF.2 j s hsj).1.1 hsyb hsyz).symm

theorem glue_injective {n D mul F P roots m v label : M.Carrier .set}
    (hMatch : Matches n D mul F P) (hReal : Realization n D mul P roots)
    (hA : Glue n D mul F roots m label) (hB : Glue n D mul F roots v label) : m = v := by
  obtain ⟨i,x,r,ri,hi,hx,hri,hRootI,hProductI,hrxa⟩ := hA
  obtain ⟨j,y,s,rj,hj,hy,hsj,hRootJ,hProductJ,hsyb⟩ := hB
  have hRel := (hMatch i x j y r s hi hx hj hy hri hsj).mp ⟨label,hrxa,hsyb⟩
  exact (hReal i j x y ri rj m v hi hj hx hy hRootI hRootJ hProductI hProductJ).mpr hRel

def glue {m : Nat} (n D mul F roots mPoint label : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound (3 : Fin (m+4))) (.bound
  n.succ.succ.succ.succ)) (.conj (.mem (.bound (2 : Fin (m+4))) (.bound D.succ.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4))))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ.succ (3 : Fin (m+4)) (0 :
  Fin (m+4)))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ (0 : Fin
  (m+4)) (2 : Fin (m+4)) mPoint.succ.succ.succ.succ)) (Project.Formula.orderedPairMem
  PureKuratowskiProject.convention (.bound (2 : Fin (m+4))) (.bound label.succ.succ.succ.succ) (.bound (1 :
  Fin (m+4)))))))))))))
theorem glue_freeClosed {m : Nat} (n D mul F roots mPoint label : Fin m) :
    (glue n D mul F roots mPoint label).FreeClosed := by
  simp -implicitDefEqProofs [glue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem glue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul F roots mPoint label : Fin m) :
    Project.Formula.satisfies env (glue n D mul F roots mPoint label) ↔
      Glue (env.bound n) (env.bound D) (env.bound mul) (env.bound F) (env.bound roots) (env.bound mPoint) (env.bound label) := by
  simp only [glue,Glue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

theorem partial_diagram (hM : FirstOrder.Theory.Models M nativeZF)
    {n D I mul F P roots : M.Carrier .set}
    (hF : Family n D I F) (hMatch : Matches n D mul F P) (hReal : Realization n D mul P roots) :
    ∃ U f, (Project.FirstOrderSemantics.reduct M).MemberSubset U D ∧ Injection U I f ∧
      ∀ m label, PureKuratowski.PairMember M m label f ↔
        (Project.FirstOrderSemantics.reduct M).mem m D ∧ Glue n D mul F roots m label := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases n (Fin.cases D (Fin.cases mul (Fin.cases F (fun _ => roots)))), free := fun _ => n }
  let schema : Project.BinarySchema 5 := { body := glue 2 3 4 5 6 1 0, freeClosed := glue_freeClosed _ _ _ _ _ _ _ }
  have hSchema m label : schema.denote env m label ↔ Glue n D mul F roots m label := by
    simpa only [Project.BinarySchema.denote,schema] using! glue_semantics hM ((env.push m).push label) 2 3 4 5 6 1 0
  let domainSchema : Project.UnarySchema 5 := {
    body := .existsE (glue 2 3 4 5 6 1 0)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,glue_freeClosed] }
  obtain ⟨U,hU⟩ := ZF.separation_exists_d hZF domainSchema env D
  have hDomain m : (Project.FirstOrderSemantics.reduct M).mem m U ↔
      (Project.FirstOrderSemantics.reduct M).mem m D ∧ ∃ label, Glue n D mul F roots m label := by
    have hd : domainSchema.denote env m ↔ ∃ label, Glue n D mul F roots m label := by
      simpa only [Project.UnarySchema.denote,domainSchema,Project.Formula.satisfies_exists_iff] using!
        exists_congr (fun label => glue_semantics hM ((env.push m).push label) 2 3 4 5 6 1 0)
    exact (hU m).trans (and_congr Iff.rfl hd)
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF pair schema env
    (source := U) (target := I) (by
      intro m hm
      obtain ⟨_,label,hLabel⟩ := (hDomain m).mp hm
      exact ⟨label,(hSchema m label).mpr hLabel⟩) (by
      intro m _ a b ha hb
      exact glue_functional hF hMatch hReal ((hSchema m a).mp ha) ((hSchema m b).mp hb)) (by
      intro m label _ h
      obtain ⟨i,x,r,_,_,_,hri,_,_,hxr⟩ := (hSchema m label).mp h
      exact (hF.2 i r hri).1.2 x label hxr)
  have hEdges m label : PureKuratowski.PairMember M m label f ↔
      (Project.FirstOrderSemantics.reduct M).mem m D ∧ Glue n D mul F roots m label := by
    constructor
    · intro h
      obtain ⟨hm,h⟩ := (he m label).mp h
      exact ⟨((hDomain m).mp hm).1,(hSchema m label).mp h⟩
    · rintro ⟨hm,h⟩
      exact (he m label).mpr ⟨(hDomain m).mpr ⟨hm,label,h⟩,(hSchema m label).mpr h⟩
  have hInj : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo pair f U I := by
    refine ⟨hf,?_⟩
    intro m v label hm hv
    exact glue_injective hMatch hReal ((hEdges m label).mp hm).2 ((hEdges v label).mp hv).2
  exact ⟨U,f,fun m hm => ((hDomain m).mp hm).1,(ForcingSupportSize.native_injection hM U I f).mpr hInj,hEdges⟩

theorem subdiagrams {n D I mul e F roots r : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : Family n D I F) (hRoots : MapsTo n D roots)
    (hr : Injection D I r)
    (hGlue : ∀ m label, (Project.FirstOrderSemantics.reduct M).mem m D →
      Glue n D mul F roots m label → PureKuratowski.PairMember M m label r) :
    Subdiagrams n D mul F roots r := by
  intro i s ri hi his hri x label
  constructor
  · intro hxl
    have hx := ForcingConditionGraphs.function_input (hF.2 i s his).1.1 hxl
    obtain ⟨m,hmD,hProd⟩ := (hm.2.1 ri (hRoots.2 i ri hri)).1 x hx
    exact ⟨hx,m,hmD,hProd,hGlue m label hmD ⟨i,x,s,ri,hi,hx,his,hri,hProd,hxl⟩⟩
  · rintro ⟨hx,m,hmD,hProd,hml⟩
    obtain ⟨other,hxo,_⟩ := (hF.2 i s his).1.1.2 x hx
    have hmo := hGlue m other hmD ⟨i,x,s,ri,hi,hx,his,hri,hProd,hxo⟩
    have he := ForcingConditionGraphs.function_unique hr.1.1 hml hmo
    simpa only [he] using hxo

theorem common_extension {n D I mul F roots r : M.Carrier .set}
    (hr : Injection D I r) (hRoots : MapsTo n D roots) (hSub : Subdiagrams n D mul F roots r) :
    CommonExtension n D I mul F r := by
  refine ⟨hr,?_⟩
  intro i s hi his
  obtain ⟨ri,hri,_⟩ := hRoots.1.2 i hi
  exact ⟨ri,hRoots.2 i ri hri,hSub i s ri hi his hri⟩

theorem amalgamate (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu history kappa D mul e mark H C incoming base n I F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small D mu)
    (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa D mul e mark H C incoming base kappa)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hm : LeftCancelMonoid D mul e)
    (hF : Family n D I F) (hExact : ExactFamily n D I mul F) :
    ∃ P identity roots r, Result n D I mul F P identity roots r := by
  obtain ⟨eWhole,hEWhole⟩ := whole_embedding hM hMu.1 hI hD
  obtain ⟨P,hP,hComplete⟩ := ConstructionDiagramPrescription.realize_family hM hChoice hMergers hRow hn hF hExact
  obtain ⟨identity,roots,hIdentityMap,hIdentity,hRoots,hRootSystem,hReal⟩ := hComplete
  obtain ⟨U,f,hUD,hf,hEdges⟩ := partial_diagram hM hF hP.2.2.2.1 hReal
  have hLarge : ¬ Small I mu := fun h => hI.not_cardinalLessOrEqual
    (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) ((ForcingSupportSize.native_small hM I mu).mp h)
  obtain ⟨r,hr,hExt⟩ := extend_embedding hM hChoice hw hMu hLarge hD hEWhole hf hUD
  have hSub := subdiagrams hm hF hRoots hr (fun m label hm h => hExt m label ((hEdges m label).mpr ⟨hm,h⟩))
  exact ⟨P,identity,roots,r,hP,hIdentityMap,hIdentity,hRoots,hRootSystem,hReal,hSub,common_extension hr hRoots hSub⟩

def subdiagramsF {m : Nat} (n D mul F roots r : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin (m+3))) (.bound n.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))
  (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ.succ.succ mul.succ.succ.succ r.succ.succ.succ (0
  : Fin (m+3)) (1 : Fin (m+3))))))))))
theorem subdiagramsF_freeClosed {m : Nat} (n D mul F roots r : Fin m) :
    (subdiagramsF n D mul F roots r).FreeClosed := by
  simp -implicitDefEqProofs [subdiagramsF,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem subdiagramsF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul F roots r : Fin m) :
    Project.Formula.satisfies env (subdiagramsF n D mul F roots r) ↔
      Subdiagrams (env.bound n) (env.bound D) (env.bound mul) (env.bound F) (env.bound roots) (env.bound r) := by
  simp only [subdiagramsF,Subdiagrams,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingDiagramOrder.sub_semantics (M := M),Project.Term.eval_bound]
  rfl

def commonExtension {m : Nat} (n D I mul F r : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.injection r D I))
    (.forallE (.forallE (.imp (.mem (.bound 1) (.bound n.succ.succ))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 1 0))
        (ProjectSyntax.encode id (ForcingDiagramOrder.le D.succ.succ mul.succ.succ r.succ.succ 0))))))

theorem commonExtension_freeClosed {m : Nat} (n D I mul F r : Fin m) :
    (commonExtension n D I mul F r).FreeClosed := by
  simp -implicitDefEqProofs [commonExtension,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem commonExtension_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D I mul F r : Fin m) :
    Project.Formula.satisfies env (commonExtension n D I mul F r) ↔
      CommonExtension (env.bound n) (env.bound D) (env.bound I) (env.bound mul) (env.bound F) (env.bound r) := by
  simp only [commonExtension,CommonExtension,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),KuratowskiZF.source_edge,
    ForcingDiagramOrder.le_semantics (M := M),Project.Term.eval_bound]
  rfl

def result {m : Nat} (n D I mul F P identity roots r : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionDiagramPrescription.result n D mul F P) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo identity D D)) (.conj (ProjectSyntax.encode id
  (ForcingConditionGraphs.identityGraph D identity)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo roots n D)) (.conj (ConstructionMergerRootSystem.rootSystem n P D mul identity
  roots) (.conj (ConstructionSaturationMergers.realization n D mul P roots) (.conj (subdiagramsF n D mul F
  roots r) (commonExtension n D I mul F r))))))))
theorem result_freeClosed {m : Nat} (n D I mul F P identity roots r : Fin m) :
    (result n D I mul F P identity roots r).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,
    ConstructionDiagramPrescription.result_freeClosed,ProjectSyntax.freeClosed,
    ConstructionMergerRootSystem.rootSystem_freeClosed,ConstructionSaturationMergers.realization_freeClosed,
    subdiagramsF_freeClosed,commonExtension_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D I mul F P identity roots r : Fin m) :
    Project.Formula.satisfies env (result n D I mul F P identity roots r) ↔
      Result (env.bound n) (env.bound D) (env.bound I) (env.bound mul) (env.bound F) (env.bound P)
        (env.bound identity) (env.bound roots) (env.bound r) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,ConstructionDiagramPrescription.result_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),
    ConstructionMergerRootSystem.rootSystem_semantics hM,ConstructionSaturationMergers.realization_semantics hM,
    subdiagramsF_semantics hM,commonExtension_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 15
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound 1)) (.imp
    (ConstructionSaturationIndex.hartogs (1 : Fin 15) 13) (.imp (ProjectSyntax.encode id
    (ForcingSupportSize.small (4 : Fin 15) 1)) (.imp (ConstructionSaturationMergers.allMergers (0 : Fin 15)
    2 3) (.imp (ConstructionTowerHistory.row (2 : Fin 15) 3 4 5 6 7 8 9 10 11 3) (.imp (.mem (.bound (12 :
    Fin 15)) (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 15) 5
    6)) (.imp (ConstructionDiagramPrescription.family (12 : Fin 15) 4 13 14) (.imp
    (ConstructionDiagramPrescription.exactFamily (12 : Fin 15) 4 13 5 14) (.existsE (.existsE (.existsE
    (.existsE (result (12 : Fin 15).succ.succ.succ.succ (4 : Fin 15).succ.succ.succ.succ (13 : Fin
    15).succ.succ.succ.succ (5 : Fin 15).succ.succ.succ.succ (14 : Fin 15).succ.succ.succ.succ 3 2 1
    0)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionDiagramPrescription.family_freeClosed,ConstructionDiagramPrescription.exactFamily_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,Project.Formula.satisfies_mem_iff,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionDiagramPrescription.family_semantics hM,ConstructionDiagramPrescription.exactFamily_semantics hM,
    result_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hI hD hMergers hRow hn hm hF hExact =>
    amalgamate hM hChoice hw hMu hI hD hMergers hRow hn hm hF hExact

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionDiagramAmalgamation
