/- Pinned MergerPushouts.IsPushout.equiv/equiv_comp_left/right and map_apex;
CellCuts.IsPushout.change_left. Actual consumers: selected restriction,
Square.presentationPushout/realization/attachment/intermediate.
Reuse existing Hom, IsPushout, InverseGraph and native graph constructors. -/
import PPAC.Migration.ConstructionPushoutPasting

namespace PPAC.Migration.ConstructionPushoutIdentification
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Hom SquareComm IsPushout composition_value)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionPushoutPasting (exists_hom_comp nodeMap_assoc square_post)
open ConstructionProbeLetters (Representatives)
open ForcingDiagramPoset (Unit Associative)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (IdentityGraph InverseGraph function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Reuse the local right_id argument from ConstructionTowerAppend:152-158. -/
theorem right_identity {A W g identity : M.Carrier .set}
    (hg : MapsTo A W g) (hId : IdentityGraph W identity) : NodeMap g identity g := by
  intro x y
  constructor
  · intro hxy
    exact ⟨y,hxy,(hId y y).mpr ⟨hg.2 x y hxy,rfl⟩⟩
  · rintro ⟨z,hxz,hzy⟩
    exact ((hId z y).mp hzy).2 ▸ hxz

/-- Equip the existing native identity graph with its literal homomorphism laws. -/
theorem exists_hom_identity (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e : M.Carrier .set} (he : (Project.FirstOrderSemantics.reduct M).mem e D) :
    ∃ ident, Hom D D mul mul e e ident ∧ IdentityGraph D ident := by
  obtain ⟨ident,hid,hgraph⟩ := ForcingConditionGraphs.exists_identity hM D
  refine ⟨ident,⟨hid.1,(hgraph e e).mpr ⟨he,rfl⟩,?_⟩,hgraph⟩
  intro x y z fx fy fz hp hx hy hz
  have hx' := ((hgraph x fx).mp hx).2
  have hy' := ((hgraph y fy).mp hy).2
  have hz' := ((hgraph z fz).mp hz).2
  subst fx; subst fy; subst fz
  exact hp

/-- Existing set-function extensionality applied to two copies of one composite. -/
theorem nodeMap_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {A Q f g s t : M.Carrier .set} (hs : MapsTo A Q s) (ht : MapsTo A Q t)
    (hS : NodeMap f g s) (hT : NodeMap f g t) : s = t :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM A Q s).mp hs).1.1
    ((ForcingSupportSize.native_mapsTo hM A Q t).mp ht).1.1
    (fun x y => (hS x y).trans (hT x y).symm)

/-- Cancel an actual pair of mutually inverse internal graphs. -/
theorem inverse_cancel {A B Q f g t s : M.Carrier .set}
    (hf : MapsTo A B f) (hg : MapsTo B A g) (hInv : InverseGraph f g)
    (ht : MapsTo A Q t) (hs : NodeMap g t s) : NodeMap f s t := by
  intro x y
  constructor
  · intro hxy
    obtain ⟨b,hxb,_⟩ := hf.1.2 x (function_input ht.1 hxy)
    exact ⟨b,hxb,(hs b y).mpr ⟨x,(hInv x b).mp hxb,hxy⟩⟩
  · rintro ⟨b,hxb,hby⟩
    obtain ⟨z,hbz,hzy⟩ := (hs b y).mp hby
    have he := function_unique hg.1 hbz ((hInv x b).mp hxb)
    exact he ▸ hzy

/-- The actual bidirectional comparison, including BOTH base equations. -/
def Comparison (D E mulD mulE eD eE bd cd be ce f g : M.Carrier .set) : Prop :=
  Hom D E mulD mulE eD eE f ∧ Hom E D mulE mulD eE eD g ∧ InverseGraph f g ∧
  NodeMap bd f be ∧ NodeMap cd f ce ∧ NodeMap be g bd ∧ NodeMap ce g cd

/-- Source equiv: construct the two lifts, then prove their composites are identities. -/
theorem exists_comparison (hM : FirstOrder.Theory.Models M nativeZF)
    {B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce : M.Carrier .set}
    (hJD : Representatives D D JD) (hMulD : MapsTo JD D mulD)
    (hUD : Unit D mulD eD) (hAD : Associative D mulD)
    (hJE : Representatives E E JE) (hMulE : MapsTo JE E mulE)
    (hUE : Unit E mulE eE) (hAE : Associative E mulE)
    (hbd : Hom B D mulB mulD eB eD bd) (hcd : Hom C D mulC mulD eC eD cd)
    (hbe : Hom B E mulB mulE eB eE be) (hce : Hom C E mulC mulE eC eE ce)
    (hD : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd)
    (hE : IsPushout C B E mulC mulB mulE eC eB eE ab ac be ce) :
    ∃ f g, Comparison D E mulD mulE eD eE bd cd be ce f g := by
  obtain ⟨f,hf,hfB,hfC,_⟩ := hD.2 E JE mulE eE be ce hJE hMulE hUE hAE hbe hce hE.1
  obtain ⟨g,hg,hgB,hgC,_⟩ := hE.2 D JD mulD eD bd cd hJD hMulD hUD hAD hbd hcd hD.1
  obtain ⟨gf,hgf,hgfGraph⟩ := exists_hom_comp hM hf hg
  obtain ⟨fg,hfg,hfgGraph⟩ := exists_hom_comp hM hg hf
  obtain ⟨idD,hIdD,hIdDGraph⟩ := exists_hom_identity (mul := mulD) hM hUD.1
  obtain ⟨idE,hIdE,hIdEGraph⟩ := exists_hom_identity (mul := mulE) hM hUE.1
  obtain ⟨u,_,_,_,hu⟩ := hD.2 D JD mulD eD bd cd hJD hMulD hUD hAD hbd hcd hD.1
  have hgfId : gf = idD :=
    (hu gf hgf ((nodeMap_assoc hfB hgfGraph).mp hgB) ((nodeMap_assoc hfC hgfGraph).mp hgC)).trans
      (hu idD hIdD (right_identity hbd.1 hIdDGraph) (right_identity hcd.1 hIdDGraph)).symm
  obtain ⟨v,_,_,_,hv⟩ := hE.2 E JE mulE eE be ce hJE hMulE hUE hAE hbe hce hE.1
  have hfgId : fg = idE :=
    (hv fg hfg ((nodeMap_assoc hgB hfgGraph).mp hfB) ((nodeMap_assoc hgC hfgGraph).mp hfC)).trans
      (hv idE hIdE (right_identity hbe.1 hIdEGraph) (right_identity hce.1 hIdEGraph)).symm
  subst gf; subst fg
  refine ⟨f,g,hf,hg,?_,hfB,hfC,hgB,hgC⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨z,hyz,_⟩ := hg.1.1.2 y (hf.1.2 x y hxy)
    have he := ((hIdDGraph x z).mp ((hgfGraph x z).mpr ⟨y,hxy,hyz⟩)).2
    exact he.symm ▸ hyz
  · intro hyx
    obtain ⟨z,hxz,_⟩ := hf.1.1.2 x (hg.1.2 y x hyx)
    have he := ((hIdEGraph y z).mp ((hfgGraph y z).mpr ⟨x,hyx,hxz⟩)).2
    exact he.symm ▸ hxz

/-- Source map_apex: transport the complete universal property through the actual isomorphism. -/
theorem map_apex (hM : FirstOrder.Theory.Models M nativeZF)
    {B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g : M.Carrier .set}
    (hf : Hom D E mulD mulE eD eE f) (hg : Hom E D mulE mulD eE eD g)
    (hInv : InverseGraph f g) (hbe : NodeMap bd f be) (hce : NodeMap cd f ce)
    (h : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) :
    IsPushout C B E mulC mulB mulE eC eB eE ab ac be ce := by
  refine ⟨square_post h.1 hbe hce,?_⟩
  intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
  obtain ⟨d,hd,hdB,hdC,hdUnique⟩ := h.2 Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
  obtain ⟨L,hL,hLGraph⟩ := exists_hom_comp hM hg hd
  have hfL : NodeMap f L d := inverse_cancel hf.1 hg.1 hInv hd.1 hLGraph
  refine ⟨L,hL,(nodeMap_assoc hbe hfL).mpr hdB,(nodeMap_assoc hce hfL).mpr hdC,?_⟩
  intro R hR hRB hRC
  obtain ⟨rD,hrD,hrDGraph⟩ := exists_hom_comp hM hf hR
  have he : rD = d := hdUnique rD hrD ((nodeMap_assoc hbe hrDGraph).mp hRB)
    ((nodeMap_assoc hce hrDGraph).mp hRC)
  subst rD
  exact nodeMap_unique hM hR.1 hL.1
    (inverse_cancel hg.1 hf.1 (fun x y => (hInv y x).symm) hR.1 hrDGraph) hLGraph

/-- Source change_left: replace the upper-right corner, keeping the actual apex. -/
theorem change_left (hM : FirstOrder.Theory.Models M nativeZF)
    {A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g : M.Carrier .set}
    (hab : MapsTo A B ab) (hbd : Hom B D mulB mulD eB eD bd)
    (hf : Hom B E mulB mulE eB eE f) (hg : Hom E B mulE mulB eE eB g)
    (hInv : InverseGraph f g) (hae : NodeMap ab f ae) (hed : NodeMap g bd ed)
    (h : IsPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) :
    IsPushout C E D mulC mulE mulD eC eE eD ae ac ed cd := by
  refine ⟨?_,?_⟩
  · intro x e c y hxe hxc
    obtain ⟨b,hxb,hbe⟩ := (hae x e).mp hxe
    exact (composition_value hg.1 hed ((hInv b e).mp hbe)).trans (h.1 x b c y hxb hxc)
  · intro Q J mulQ eQ s t hJ hMul hUnit hAssoc hs ht hc
    obtain ⟨sb,hsb,hsbGraph⟩ := exists_hom_comp hM hf hs
    have hsq : SquareComm ab ac sb t := by
      intro x b c y hxb hxc
      obtain ⟨e,hbe,_⟩ := hf.1.1.2 b (hab.2 x b hxb)
      exact (composition_value hf.1 hsbGraph hbe).trans
        (hc x e c y ((hae x e).mpr ⟨b,hxb,hbe⟩) hxc)
    obtain ⟨L,hL,hLB,hLC,hUnique⟩ := h.2 Q J mulQ eQ sb t hJ hMul hUnit hAssoc hsb ht hsq
    have hgs : NodeMap g sb s := inverse_cancel hg.1 hf.1 (fun x y => (hInv y x).symm) hs.1 hsbGraph
    refine ⟨L,hL,(nodeMap_assoc hed hLB).mpr hgs,hLC,?_⟩
    intro R hR hRE hRC
    obtain ⟨rb,hrb,hrbGraph⟩ := exists_hom_comp hM hbd hR
    have hgrb : NodeMap g rb s := (nodeMap_assoc hed hrbGraph).mp hRE
    have he : rb = sb := nodeMap_unique hM hrb.1 hsb.1
      (inverse_cancel hf.1 hg.1 hInv hrb.1 hgrb) hsbGraph
    subst rb
    exact hUnique R hR hrbGraph hRC

def comparison {m : Nat} (D E mulD mulE eD eE bd cd be ce f g : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbePushoutSyntax.hom D E mulD mulE eD eE f) (.conj (ConstructionProbePushoutSyntax.hom E D mulE mulD eE eD g) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph f g)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap bd f be) (.conj (ConstructionProbeMappedPathSyntax.nodeMap cd f ce) (.conj (ConstructionProbeMappedPathSyntax.nodeMap be g bd) (ConstructionProbeMappedPathSyntax.nodeMap ce g cd)))))))

theorem comparison_freeClosed {m : Nat} (D E mulD mulE eD eE bd cd be ce f g : Fin m) : (comparison D E mulD mulE eD eE bd cd be ce f g).FreeClosed := by
  simp -implicitDefEqProofs [comparison, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed, ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem comparison_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D E mulD mulE eD eE bd cd be ce f g : Fin m) :
    Project.Formula.satisfies env (comparison D E mulD mulE eD eE bd cd be ce f g) ↔
      Comparison (env.bound D) (env.bound E) (env.bound mulD) (env.bound mulE) (env.bound eD) (env.bound eE) (env.bound bd) (env.bound cd) (env.bound be) (env.bound ce) (env.bound f) (env.bound g) := by
  simp only [comparison, Comparison, Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl

def comparisonSentence {m : Nat} (B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionProbeLetters.representatives D D JD) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo mulD JD D)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit D mulD eD)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.associative D mulD)) (.imp (ConstructionProbeLetters.representatives E E JE) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo mulE JE E)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit E mulE eE)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.associative E mulE)) (.imp (ConstructionProbePushoutSyntax.hom B D mulB mulD eB eD bd) (.imp (ConstructionProbePushoutSyntax.hom C D mulC mulD eC eD cd) (.imp (ConstructionProbePushoutSyntax.hom B E mulB mulE eB eE be) (.imp (ConstructionProbePushoutSyntax.hom C E mulC mulE eC eE ce) (.imp (ConstructionProbePushoutSyntax.isPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) (.imp (ConstructionProbePushoutSyntax.isPushout C B E mulC mulB mulE eC eB eE ab ac be ce) (.existsE (.existsE (comparison D.succ.succ E.succ.succ mulD.succ.succ mulE.succ.succ eD.succ.succ eE.succ.succ bd.succ.succ cd.succ.succ be.succ.succ ce.succ.succ 1 0)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed, ConstructionProbePushoutSyntax.isPushout_freeClosed,
      comparison_freeClosed]

theorem comparison_models {m : Nat} (B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (comparisonSentence B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (comparisonSentence B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M), ForcingDiagramPoset.unit_semantics (M := M),
    ForcingDiagramPoset.associative_semantics (M := M),
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM, ConstructionProbePushoutSyntax.isPushout_semantics hM,
    comparison_semantics hM]
  exact exists_comparison hM

theorem comparison_kernel_certificate {m : Nat} (B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (comparisonSentence B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce)) :=
  ModelTransfer.derives (fun _ hM => comparison_models B C D E JD JE mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce hM)

def apexSentence {m : Nat} (B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionProbePushoutSyntax.hom D E mulD mulE eD eE f) (.imp (ConstructionProbePushoutSyntax.hom E D mulE mulD eE eD g) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph f g)) (.imp (ConstructionProbeMappedPathSyntax.nodeMap bd f be) (.imp (ConstructionProbeMappedPathSyntax.nodeMap cd f ce) (.imp (ConstructionProbePushoutSyntax.isPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) (ConstructionProbePushoutSyntax.isPushout C B E mulC mulB mulE eC eB eE ab ac be ce)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed, ConstructionProbePushoutSyntax.isPushout_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem apex_models {m : Nat} (B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (apexSentence B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (apexSentence B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbePushoutSyntax.hom_semantics hM, ConstructionProbePushoutSyntax.isPushout_semantics hM,
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact map_apex hM

theorem apex_kernel_certificate {m : Nat} (B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (apexSentence B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g)) :=
  ModelTransfer.derives (fun _ hM => apex_models B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd be ce f g hM)

def leftSentence {m : Nat} (A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo ab A B)) (.imp (ConstructionProbePushoutSyntax.hom B D mulB mulD eB eD bd) (.imp (ConstructionProbePushoutSyntax.hom B E mulB mulE eB eE f) (.imp (ConstructionProbePushoutSyntax.hom E B mulE mulB eE eB g) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph f g)) (.imp (ConstructionProbeMappedPathSyntax.nodeMap ab f ae) (.imp (ConstructionProbeMappedPathSyntax.nodeMap g bd ed) (.imp (ConstructionProbePushoutSyntax.isPushout C B D mulC mulB mulD eC eB eD ab ac bd cd) (ConstructionProbePushoutSyntax.isPushout C E D mulC mulE mulD eC eE eD ae ac ed cd)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed, ConstructionProbePushoutSyntax.isPushout_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem left_models {m : Nat} (A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (leftSentence A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (leftSentence A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM, ConstructionProbePushoutSyntax.isPushout_semantics hM,
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact change_left hM

theorem left_kernel_certificate {m : Nat} (A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (leftSentence A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g)) :=
  ModelTransfer.derives (fun _ hM => left_models A B C D E mulB mulC mulD mulE eB eC eD eE ab ac bd cd ae ed f g hM)

end PPAC.Migration.ConstructionPushoutIdentification
