/- Pinned MergerPushouts.OverlapPrescription.satisfies_rel/interpretedCopy/
interpretedCopy_act/presentedLift/existsUnique_presentedHom.
Consumer: mergerSimulation_pushout and ConservativeCells.Merger.
Use the actual existing Copies quotient, root graph and internal word fold. -/
import PPAC.Migration.ConstructionMergerEvaluation
import PPAC.Migration.ConstructionMergerRoots

namespace PPAC.Migration.ConstructionMergerPresentedLift
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_indices projected_range)
open ConstructionProbeHomEvaluation (product_unique)
open ConstructionProbePushout (Hom)
open ConstructionMergerRelations (Start Prescription CopyRel)
open ConstructionMergerCopies (Copies Projection EqualityLaw representative copy_eq_iff)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_unique function_input)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (Unit Associative LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The literal source value p i * f x, represented by internal graphs. -/
def Value (f p mulN i x v : M.Carrier .set) : Prop :=
  ∃ pi fx, PureKuratowski.PairMember M i pi p ∧ PureKuratowski.PairMember M x fx f ∧ Product mulN pi fx v

/-- Only off-diagonal prescribed start relations are imposed on the target. -/
def Satisfies (P f p mulN : M.Carrier .set) : Prop :=
  ∀ i j a b u v, i ≠ j → Start P i j a b → Value f p mulN i a u → Value f p mulN j b v → u = v

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D n N J f p mulN i x u v : M.Carrier .set}
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hMul : MapsTo J N mulN)
    (hu : Value f p mulN i x u) (hv : Value f p mulN i x v) : u = v := by
  obtain ⟨pi,fx,hi,hx,hu⟩ := hu
  obtain ⟨pi',fx',hi',hx',hv⟩ := hv
  have hiEq := function_unique hp.1 hi' hi
  have hxEq := function_unique hf.1 hx' hx
  subst pi'
  subst fx'
  exact product_unique hM hMul hu hv

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {D n N J f p mulN i x : M.Carrier .set}
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hJ : Representatives N N J) (hMul : MapsTo J N mulN)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i n) (hx : (Project.FirstOrderSemantics.reduct M).mem x D) :
    ∃ v, Value f p mulN i x v := by
  obtain ⟨pi,hi',_⟩ := hp.1.2 i hi
  obtain ⟨fx,hx',_⟩ := hf.1.2 x hx
  obtain ⟨v,_,hv⟩ := projected hM hJ hMul (hp.2 i pi hi') (hf.2 x fx hx')
  exact ⟨v,pi,fx,hi',hx',hv⟩

theorem value_mul
    {D n N mul f p mulN i x t xt u ft v : M.Carrier .set}
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hAssoc : Associative N mulN)
    (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hxt : Product mul x t xt) (hu : Value f p mulN i x u)
    (ht : PureKuratowski.PairMember M t ft f) (hv : Value f p mulN i xt v) :
    Product mulN u ft v := by
  obtain ⟨pi,fx,hi,hx,hu⟩ := hu
  obtain ⟨pi',fxt,hi',hxt',hv⟩ := hv
  have he := function_unique hp.1 hi' hi
  subst pi'
  have hProd := hPres x t xt fx ft fxt hxt hx ht hxt'
  exact (hAssoc pi fx ft u fxt v (hp.2 i pi hi) (hf.2 x fx hx) (hf.2 t ft ht) hu hProd).mpr hv

theorem satisfies_rel (hM : FirstOrder.Theory.Models M nativeZF)
    {D n N J mul P f p mulN i x j y u v : M.Carrier .set}
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hJ : Representatives N N J) (hMul : MapsTo J N mulN)
    (hAssoc : Associative N mulN) (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hP : Prescription n D P) (hSat : Satisfies P f p mulN)
    (hRel : CopyRel n D mul P i x j y) (hu : Value f p mulN i x u) (hv : Value f p mulN j y v) : u = v := by
  obtain ⟨hi,_,hj,_,hRel⟩ := hRel
  rcases hRel with ⟨rfl,rfl⟩ | ⟨hne,a,b,t,hStart,ht,hat,hbt⟩
  · exact value_unique hM hf hp hMul hu hv
  · obtain ⟨_,_,ha,hb⟩ := hP.1 i j a b hStart
    obtain ⟨ua,hua⟩ := value_total hM hf hp hJ hMul hi ha
    obtain ⟨ub,hub⟩ := value_total hM hf hp hJ hMul hj hb
    have he := hSat i j a b ua ub hne hStart hua hub
    subst ub
    obtain ⟨ft,hft,_⟩ := hf.1.2 t ht
    exact product_unique hM hMul (value_mul hf hp hAssoc hPres hat hua hft hu)
      (value_mul hf hp hAssoc hPres hbt hub hft hv)

def CopyValue (projection f p mulN c v : M.Carrier .set) : Prop :=
  ∃ i x, Product projection i x c ∧ Value f p mulN i x v

def CopyEvaluation (projection f p mulN g : M.Carrier .set) : Prop :=
  ∀ i x c v, Product projection i x c → (PureKuratowski.PairMember M c v g ↔ Value f p mulN i x v)

def value {m : Nat} (f p mulN i x v : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge p.succ.succ i.succ.succ 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ x.succ.succ 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product mulN.succ.succ 1 0 v.succ.succ)))))

theorem value_freeClosed {m : Nat} (f p mulN i x v : Fin m) : (value f p mulN i x v).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f p mulN i x v : Fin m) :
    Project.Formula.satisfies env (value f p mulN i x v) ↔ Value (env.bound f) (env.bound p) (env.bound mulN) (env.bound i) (env.bound x) (env.bound v) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def copyValue {m : Nat} (projection f p mulN c v : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ 1 0 c.succ.succ)) (value f.succ.succ p.succ.succ mulN.succ.succ 1 0 v.succ.succ)))

theorem copyValue_freeClosed {m : Nat} (projection f p mulN c v : Fin m) : (copyValue projection f p mulN c v).FreeClosed := by
  simp -implicitDefEqProofs [copyValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed ,value_freeClosed]

theorem copyValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (projection f p mulN c v : Fin m) :
    Project.Formula.satisfies env (copyValue projection f p mulN c v) ↔ CopyValue (env.bound projection) (env.bound f) (env.bound p) (env.bound mulN) (env.bound c) (env.bound v) := by
  simp only [copyValue,CopyValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),value_semantics hM]
  rfl

def satisfies {m : Nat} (P f p mulN : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE ((.imp (.neg (Project.Formula.extensionalEq (.bound 5) (.bound 4))) (.imp (ConstructionMergerRelations.start P.succ.succ.succ.succ.succ.succ 5 4 3 2) (.imp (value f.succ.succ.succ.succ.succ.succ p.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ 5 3 1) (.imp (value f.succ.succ.succ.succ.succ.succ p.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ 4 2 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))))))

theorem satisfies_freeClosed {m : Nat} (P f p mulN : Fin m) : (satisfies P f p mulN).FreeClosed := by
  simp -implicitDefEqProofs [satisfies,Definitional.Formula.FreeClosed,value_freeClosed ,Project.Formula.extensionalEq,ConstructionMergerRelations.start_freeClosed]

theorem satisfies_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P f p mulN : Fin m) :
    Project.Formula.satisfies env (satisfies P f p mulN) ↔ Satisfies (env.bound P) (env.bound f) (env.bound p) (env.bound mulN) := by
  simp only [satisfies,Satisfies,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),value_semantics hM,ConstructionMergerRelations.start_semantics hM]
  rfl

def copyEvaluation {m : Nat} (projection f p mulN g : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE ((.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ.succ 3 2 1)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ.succ.succ 1 0)) (value f.succ.succ.succ.succ p.succ.succ.succ.succ mulN.succ.succ.succ.succ 3 2 0)))))))

theorem copyEvaluation_freeClosed {m : Nat} (projection f p mulN g : Fin m) : (copyEvaluation projection f p mulN g).FreeClosed := by
  simp -implicitDefEqProofs [copyEvaluation,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed ,value_freeClosed]

theorem copyEvaluation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (projection f p mulN g : Fin m) :
    Project.Formula.satisfies env (copyEvaluation projection f p mulN g) ↔ CopyEvaluation (env.bound projection) (env.bound f) (env.bound p) (env.bound mulN) (env.bound g) := by
  simp only [copyEvaluation,CopyEvaluation,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge,value_semantics hM]
  rfl

/-- Construct the interpretation of the actual quotient; no representatives
are chosen and no external quotient or choice function is introduced. -/
theorem exists_copy_evaluation (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul P C L projection N J mulN f p : M.Carrier .set}
    (hC : Representatives n D C) (hL : Copies n D mul P C L)
    (hProjection : Projection n D mul P C projection) (hProj : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hf : MapsTo D N f) (hp : MapsTo n N p)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hAssoc : Associative N mulN)
    (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hP : Prescription n D P) (hSat : Satisfies P f p mulN) :
    ∃ g, MapsTo L N g ∧ CopyEvaluation projection f p mulN g := by
  have hUnique c u v (hu : CopyValue projection f p mulN c u) (hv : CopyValue projection f p mulN c v) : u = v := by
    obtain ⟨i,x,hic,hu⟩ := hu
    obtain ⟨j,y,hjc,hv⟩ := hv
    exact satisfies_rel hM hf hp hJ hMul hAssoc hPres hP hSat ((copy_eq_iff hEq hic hjc).mp rfl) hu hv
  let schema : Project.BinarySchema 4 := {
    body := copyValue 2 3 4 5 1 0, freeClosed := copyValue_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases projection (Fin.cases f (Fin.cases p (fun _ => mulN))),free := fun _ => L }
  have he c v : schema.denote env c v ↔ CopyValue projection f p mulN c v :=
    copyValue_semantics hM (env.push c |>.push v) 2 3 4 5 1 0
  obtain ⟨g,hg,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env
    (source := L) (target := N) (by
      intro c hc
      obtain ⟨i,x,hi,hx,hic⟩ := representative hC hL hProjection hc
      obtain ⟨v,hv⟩ := value_total hM hf hp hJ hMul hi hx
      exact ⟨v,(he c v).mpr ⟨i,x,hic,hv⟩⟩) (by
      intro c _ u v hu hv
      exact hUnique c u v ((he c u).mp hu) ((he c v).mp hv)) (by
      intro c v _ hv
      obtain ⟨_,_,_,_,_,_,_,hv⟩ := (he c v).mp hv
      exact projected_range hMul hv)
  refine ⟨g,(ForcingSupportSize.native_mapsTo hM L N g).mpr hg,?_⟩
  intro i x c v hic
  constructor
  · intro hv
    obtain ⟨hi,hx⟩ := projected_indices hC hProj hic
    obtain ⟨v',hv'⟩ := value_total hM hf hp hJ hMul hi hx
    have heq := hUnique c v' v ⟨i,x,hic,hv'⟩ ((he c v).mp ((hGraph c v).mp hv).2)
    exact heq ▸ hv'
  · intro hv
    exact (hGraph c v).mpr ⟨projected_range hProj hic,(he c v).mpr ⟨i,x,hic,hv⟩⟩

theorem interpretedCopy_act
    {D n N mul A projection f p mulN g : M.Carrier .set}
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hAssoc : Associative N mulN)
    (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hA : ConstructionMergerAction.ActionTable D mul projection A)
    (hg : CopyEvaluation projection f p mulN g) : ConstructionMergerEvaluation.Equivariant A f g mulN := by
  intro c t ct gc ft gct hct hc ht hgc
  obtain ⟨_,i,x,xt,_,hix,hxt,hixt⟩ := (hA c t ct).mp hct
  exact value_mul hf hp hAssoc hPres hxt ((hg i x c gc hix).mp hc) ht ((hg i xt ct gct hixt).mp hgc)

open ConstructionProbeRaw (Carrier Old Cons)
open ConstructionMergerRoots (RootGraph)

def PresentedBoundary (zero D roots f p F : M.Carrier .set) : Prop :=
  (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y F ↔ PureKuratowski.PairMember M x y f)) ∧
  ∀ i r y, PureKuratowski.PairMember M i r roots → (PureKuratowski.PairMember M r y F ↔ PureKuratowski.PairMember M i y p)

theorem presented_boundary
    {w D L zero e unit projection roots n N mulN eN f p g F : M.Carrier .set}
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hfOne : PureKuratowski.PairMember M e eN f)
    (hUN : Unit N mulN eN) (hRoots : RootGraph w D L e projection unit roots)
    (hg : CopyEvaluation projection f p mulN g)
    (hB : ConstructionMergerEvaluation.Boundary w D L zero unit f g F) :
    PresentedBoundary zero D roots f p F := by
  refine ⟨hB.1,?_⟩
  intro i r y hir
  obtain ⟨c,hic,hCons⟩ := (hRoots i r).mp hir
  rw [hB.2 c r y hCons,hg i e c y hic]
  constructor
  · rintro ⟨pi,fe,hi,he,hProd⟩
    have hEq := function_unique hf.1 he hfOne
    subst fe
    have hy := ((hUN.2 pi (hp.2 i pi hi) y).2).mp hProd
    exact hy.symm ▸ hi
  · intro hi
    exact ⟨y,eN,hi,hfOne,((hUN.2 y (hp.2 i y hi) y).2).mpr rfl⟩

/-- The source root_mul_old identity turns root and old boundary data into
ALL single-letter boundary data, for an arbitrary target homomorphism. -/
theorem word_boundary (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p g F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hW : Carrier w D L W) (hm : LeftCancelMonoid D mul e)
    (hC : Representatives n D C) (hL : Copies n D mul P C L)
    (hProjection : Projection n D mul P C projection)
    (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hTable : ConstructionMergerWordAction.ActionTable w D L zero mul A T)
    (hProduct : ConstructionMergerWordProduct.Laws w D L zero T H)
    (hRootsMap : MapsTo n W roots) (hRoots : RootGraph w D L e projection unit roots)
    (hf : MapsTo D N f) (hp : MapsTo n N p) (hg : MapsTo L N g)
    (hMul : MapsTo J N mulN) (hG : CopyEvaluation projection f p mulN g)
    (hF : Hom W N H mulN unit eN F) (hB : PresentedBoundary zero D roots f p F) :
    ConstructionMergerEvaluation.Boundary w D L zero unit f g F := by
  refine ⟨hB.1,?_⟩
  intro c q y hCons
  have hc : (Project.FirstOrderSemantics.reduct M).mem c L := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hc,_⟩ := hCons
    exact hc
  obtain ⟨i,x,hi,hx,hic⟩ := representative hC hL hProjection hc
  obtain ⟨r,hir,_⟩ := hRootsMap.1.2 i hi
  obtain ⟨ox,hOld⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hx
  have hProd : Product H r ox q := (ConstructionMergerRoots.root_mul_old hM hw hz hm hCopy hTable hProduct
    ((hRoots i r).mp hir) hOld).mpr ⟨c,hic,hCons⟩
  obtain ⟨pi,hpi,_⟩ := hp.1.2 i hi
  obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
  obtain ⟨gc,hgc,_⟩ := hg.1.2 c hc
  have hValue := (hG i x c gc hic).mp hgc
  obtain ⟨pi',fx',hpi',hfx',hV⟩ := hValue
  have hpiEq := function_unique hp.1 hpi' hpi
  have hfxEq := function_unique hf.1 hfx' hfx
  subst pi'
  subst fx'
  have hFr := (hB.2 i r pi hir).mpr hpi
  have hFo := (hB.1 x ox fx hOld).mpr hfx
  constructor
  · intro hFy
    have hy := product_unique hM hMul (hF.2.2 r ox q pi fx y hProd hFr hFo hFy) hV
    exact hy.symm ▸ hgc
  · intro hgy
    have hy := function_unique hg.1 hgy hgc
    subst y
    obtain ⟨v,hv,_⟩ := hF.1.1.2 q ((hW q).mpr (ConstructionProbeRaw.cons_raw hCons).2)
    have hvEq := product_unique hM hMul (hF.2.2 r ox q pi fx v hProd hFr hFo hv) hV
    exact hvEq ▸ hv

/-- Fixed-source existsUnique_presentedHom, now for the literal internal
Merger carrier and its actual old/root maps. Target need not be cancellative. -/
theorem existsUnique_presentedHom (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hm : LeftCancelMonoid D mul e)
    (hC : Representatives n D C) (hL : Copies n D mul P C L)
    (hProjection : Projection n D mul P C projection) (hProj : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hP : Prescription n D P)
    (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hA : ConstructionMergerAction.ActionTable D mul projection A)
    (hTable : ConstructionMergerWordAction.ActionTable w D L zero mul A T)
    (hProduct : ConstructionMergerWordProduct.Laws w D L zero T H)
    (hUnit : Old zero D e unit) (hUW : Unit W H unit)
    (hRootsMap : MapsTo n W roots) (hRoots : RootGraph w D L e projection unit roots)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN)
    (hUN : Unit N mulN eN) (hAssoc : Associative N mulN)
    (hf : Hom D N mul mulN e eN f) (hp : MapsTo n N p) (hSat : Satisfies P f p mulN) :
    ∃ F, Hom W N H mulN unit eN F ∧ PresentedBoundary zero D roots f p F ∧
      ∀ K, Hom W N H mulN unit eN K → PresentedBoundary zero D roots f p K → K = F := by
  obtain ⟨g,hg,hG⟩ := exists_copy_evaluation hM hC hL hProjection hProj hEq hf.1 hp hJ hMul hAssoc hf.2.2 hP hSat
  obtain ⟨F,hF,hB,hUnique⟩ := ConstructionMergerEvaluation.existsUnique_lift hM hw hz hzw hW hUnit hUW
    hTable hProduct hJ hMul hUN hAssoc hf hg (interpretedCopy_act hf.1 hp hAssoc hf.2.2 hA hG)
  refine ⟨F,hF,presented_boundary hf.1 hp hf.2.1 hUN hRoots hG hB,?_⟩
  intro K hK hBK
  exact hUnique K hK (word_boundary hM hw hz hW hm hC hL hProjection hCopy hTable hProduct
    hRootsMap hRoots hf.1 hp hg hMul hG hK hBK)

def presentedBoundary {m : Nat} (zero D roots f p F : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ D.succ.succ.succ 2 1) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ 2 0))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ 2 1)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge p.succ.succ.succ 2 0))))))))

theorem presentedBoundary_freeClosed {m : Nat} (zero D roots f p F : Fin m) :
    (presentedBoundary zero D roots f p F).FreeClosed := by
  simp -implicitDefEqProofs [presentedBoundary,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.old_freeClosed]

theorem presentedBoundary_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D roots f p F : Fin m) :
    Project.Formula.satisfies env (presentedBoundary zero D roots f p F) ↔ PresentedBoundary (env.bound zero) (env.bound D) (env.bound roots) (env.bound f) (env.bound p) (env.bound F) := by
  simp only [presentedBoundary,PresentedBoundary,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbeRaw.old_semantics hM]
  rfl

def sourceSentence {m : Nat} (w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem
    (.bound zero) (.bound w)) (.imp (ConstructionProbeRaw.carrier w D L W) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeLetters.representatives n D C)
    (.imp (ConstructionMergerCopies.copies n D mul P C L) (.imp (ConstructionMergerCopies.projectionGraph n D
    mul P C projection) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo projection C L)) (.imp
    (ConstructionMergerCopies.equalityLaw n D mul P projection) (.imp
    (ConstructionMergerRelations.prescription n D P) (.imp (ConstructionMergerAction.copyLaw D mul projection
    A) (.imp (ConstructionMergerAction.actionTable D mul projection A) (.imp
    (ConstructionMergerWordAction.actionTable w D L zero mul A T) (.imp (ConstructionMergerWordProduct.laws w
    D L zero T H) (.imp (ConstructionProbeRaw.old zero D e unit) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.unit W H unit)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo roots n W))
    (.imp (ConstructionMergerRoots.rootGraph w D L e projection unit roots) (.imp
    (ConstructionProbeLetters.representatives N N J) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    mulN J N)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit N mulN eN)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.associative N mulN)) (.imp
    (ConstructionProbePushoutSyntax.hom D N mul mulN e eN f) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo p n N)) (.imp (satisfies P f p mulN) (.existsE (.conj
    (ConstructionProbePushoutSyntax.hom W.succ N.succ H.succ mulN.succ unit.succ eN.succ 0) (.conj
    (presentedBoundary zero.succ D.succ roots.succ f.succ p.succ 0) (.forallE (.imp
    (ConstructionProbePushoutSyntax.hom W.succ.succ N.succ.succ H.succ.succ mulN.succ.succ unit.succ.succ
    eN.succ.succ 0) (.imp (presentedBoundary zero.succ.succ D.succ.succ roots.succ.succ f.succ.succ
    p.succ.succ 0) (Project.Formula.extensionalEq (.bound 0) (.bound 1))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isEmpty,
      Project.Formula.extensionalEq,
      ConstructionProbeRaw.carrier_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionMergerCopies.copies_freeClosed,
      ConstructionMergerCopies.projectionGraph_freeClosed,
      ConstructionMergerCopies.equalityLaw_freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,
      ConstructionMergerAction.copyLaw_freeClosed,
      ConstructionMergerAction.actionTable_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,
      ConstructionMergerWordProduct.laws_freeClosed,
      ConstructionProbeRaw.old_freeClosed,
      ConstructionMergerRoots.rootGraph_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      satisfies_freeClosed,
      presentedBoundary_freeClosed]

theorem source_models {m : Nat} (w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (sourceSentence w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbeRaw.carrier_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,
    ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,
    ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerAction.copyLaw_semantics hM,
    ConstructionMergerAction.actionTable_semantics hM,
    ConstructionMergerWordAction.actionTable_semantics hM,
    ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeRaw.old_semantics hM,
    ConstructionMergerRoots.rootGraph_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    satisfies_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.unit_semantics (M := M),
    ForcingDiagramPoset.associative_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    presentedBoundary_semantics hM]
  exact existsUnique_presentedHom hM

theorem source_kernel_certificate {m : Nat} (w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p)) :=
  ModelTransfer.derives (fun _ hM => source_models w n D L zero mul A e C P W T H projection unit roots N J mulN eN f p hM)

end PPAC.Migration.ConstructionMergerPresentedLift
