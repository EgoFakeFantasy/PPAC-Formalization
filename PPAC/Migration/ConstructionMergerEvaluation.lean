/- Pinned MergerPushouts.Word.evaluate/evaluate_act/evaluate_mul/liftHom/hom_ext.
Consumer: OverlapPrescription.presentedLift and mergerSimulation_pushout.
Reuse the existing internal Eval and formula-indexed Raw induction; preserve
literal snoc order and arbitrary internal target monoids. -/
import PPAC.Migration.ConstructionMergerWordMonoid
import PPAC.Migration.ConstructionProbePushoutSyntax

namespace PPAC.Migration.ConstructionMergerEvaluation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range projected_indices)
open ConstructionProbeHomEvaluation (Eval product_unique)
open ConstructionProbePushout (Hom)
open ConstructionMergerWordAction (ActionTable)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (Unit Associative)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Adapt the existing generic binary fold to snoc: the step graph receives
(letter value, accumulator), and returns accumulator * letter value. -/
theorem snoc_operation (hM : FirstOrder.Theory.Models M nativeZF)
    {N J mulN : M.Carrier .set} (hJ : Representatives N N J) (hMul : MapsTo J N mulN) :
    ∃ op, MapsTo J N op ∧ ∀ x y z, Product op x y z ↔ Product mulN y x z := by
  let schema : Project.BinarySchema 1 := {
    body := .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 3) (.bound 1) (.bound 0))
      (ProjectSyntax.encode id (ForcingDiagramOrder.product 4 0 1 2))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => mulN,fun _ => N⟩
  have he p z : schema.denote env p z ↔ ∃ x y, PureKuratowski.Code M p x y ∧ Product mulN y x z := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,KuratowskiZF.code_correct hM,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
    rfl
  obtain ⟨op,hOp,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env
    (source := J) (target := N) (by
      intro p hp
      obtain ⟨x,y,hx,hy,hp⟩ := (hJ p).mp hp
      obtain ⟨z,_,hz⟩ := projected hM hJ hMul hy hx
      exact ⟨z,(he p z).mpr ⟨x,y,hp,hz⟩⟩) (by
      intro p _ z t hz ht
      obtain ⟨x,y,hp,hz⟩ := (he p z).mp hz
      obtain ⟨x',y',hp',ht⟩ := (he p t).mp ht
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact product_unique hM hMul hz ht) (by
      intro p z _ hz
      obtain ⟨x,y,_,hz⟩ := (he p z).mp hz
      exact projected_range hMul hz)
  refine ⟨op,(ForcingSupportSize.native_mapsTo hM J N op).mpr hOp,?_⟩
  intro x y z
  constructor
  · rintro ⟨p,hp,hpz⟩
    obtain ⟨x',y',hp',hz⟩ := (he p z).mp ((hGraph p z).mp hpz).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    exact hz
  · intro hz
    obtain ⟨hy,hx⟩ := projected_indices hJ hMul hz
    obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM x y
    exact ⟨p,hp,(hGraph p z).mpr ⟨(hJ p).mpr ⟨x,y,hx,hy,hp⟩,(he p z).mpr ⟨x,y,hp,hz⟩⟩⟩

def EvaluationLaws (w D S zero mulN f g F : M.Carrier .set) : Prop :=
  (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y F ↔ PureKuratowski.PairMember M x y f)) ∧
  ∀ s t q y, Cons w D S s t q → (PureKuratowski.PairMember M q y F ↔
    ∃ v gs, PureKuratowski.PairMember M t v F ∧ PureKuratowski.PairMember M s gs g ∧ Product mulN v gs y)

/-- Build the evaluation graph on the SAME complete Raw carrier. No supplied
fold graph, external finite length or new recursion backend is used. -/
theorem exists_evaluation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero W N J mulN f g : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D S W) (hJ : Representatives N N J) (hMul : MapsTo J N mulN)
    (hf : MapsTo D N f) (hg : MapsTo S N g) :
    ∃ F, MapsTo W N F ∧ EvaluationLaws w D S zero mulN f g F := by
  obtain ⟨op,hOp,hSwap⟩ := snoc_operation hM hJ hMul
  let schema : Project.BinarySchema 7 := {
    body := ConstructionProbeHomEvaluationSyntax.eval 2 3 4 5 6 7 8 1 0
    freeClosed := ConstructionProbeHomEvaluationSyntax.eval_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases N (Fin.cases op (Fin.cases f (fun _ => g)))))),
    free := fun _ => w }
  have he q y : schema.denote env q y ↔ Eval hM w D S N op f g q y :=
    ConstructionProbeHomEvaluationSyntax.eval_semantics hM (env.push q |>.push y) 2 3 4 5 6 7 8 1 0
  obtain ⟨F,hF,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env
    (source := W) (target := N) (by
      intro q hq
      obtain ⟨y,hy⟩ := ConstructionProbeHomEvaluation.eval_total hM hw hJ hOp hf hg ((hW q).mp hq)
      exact ⟨y,(he q y).mpr hy⟩) (by
      intro q _ y z hy hzv
      exact ConstructionProbeHomEvaluation.eval_unique hM hw hJ hOp hf hg ((he q y).mp hy) ((he q z).mp hzv)) (by
      intro q y _ hy
      exact ConstructionProbeHomEvaluation.eval_range hM ((he q y).mp hy))
  have hGraph' q y : PureKuratowski.PairMember M q y F ↔
      (Project.FirstOrderSemantics.reduct M).mem q W ∧ Eval hM w D S N op f g q y :=
    (hGraph q y).trans (and_congr_right fun _ => he q y)
  refine ⟨F,(ForcingSupportSize.native_mapsTo hM W N F).mpr hF,?_,?_⟩
  · intro x q y hOld
    have hq := (hW q).mpr (ConstructionProbeRaw.old_raw hM hz hzw hOld)
    exact (hGraph' q y).trans ((and_iff_right hq).trans
      (ConstructionProbeHomEvaluation.eval_old_iff hM hw hz hzw hJ hOp hf hg hOld))
  · intro s t q y hCons
    have ht := (hW t).mpr (ConstructionProbeRaw.cons_raw hCons).1
    have hq := (hW q).mpr (ConstructionProbeRaw.cons_raw hCons).2
    rw [hGraph',and_iff_right hq,ConstructionProbeHomEvaluation.eval_cons_iff hM hw hJ hOp hf hg hCons]
    constructor
    · rintro ⟨v,hv,gs,hgs,hProd⟩
      exact ⟨v,gs,(hGraph' t v).mpr ⟨ht,hv⟩,hgs,(hSwap gs v y).mp hProd⟩
    · rintro ⟨v,gs,hv,hgs,hProd⟩
      exact ⟨v,((hGraph' t v).mp hv).2,gs,hgs,(hSwap gs v y).mpr hProd⟩

/-- The source right-action equivariance equation. -/
def Equivariant (A f g mulN : M.Carrier .set) : Prop := ∀ s x sx gs fx gsx,
  Product A s x sx → PureKuratowski.PairMember M s gs g → PureKuratowski.PairMember M x fx f →
    PureKuratowski.PairMember M sx gsx g → Product mulN gs fx gsx

theorem evaluate_act
    {w D S zero mul A W N mulN f g F T q x qx fq fx fqx : M.Carrier .set}
    (hF : MapsTo W N F) (hf : MapsTo D N f) (hg : MapsTo S N g)
    (hAssoc : Associative N mulN) (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hEq : Equivariant A f g mulN) (hTable : ActionTable w D S zero mul A T)
    (hL : EvaluationLaws w D S zero mulN f g F)
    (hAct : Product T q x qx) (hq : PureKuratowski.PairMember M q fq F)
    (hx : PureKuratowski.PairMember M x fx f) (hqx : PureKuratowski.PairMember M qx fqx F) :
    Product mulN fq fx fqx := by
  rcases ((hTable q x qx).mp hAct).2 with ⟨a,ax,hOld,hProd,hOut⟩ | ⟨s,t,sx,hCons,hProd,hOut⟩
  · exact hPres a x ax fq fx fqx hProd ((hL.1 a q fq hOld).mp hq) hx ((hL.1 ax qx fqx hOut).mp hqx)
  · obtain ⟨v,gs,hv,hgs,hvgs⟩ := (hL.2 s t q fq hCons).mp hq
    obtain ⟨v',gsx,hv',hgsx,hvgsx⟩ := (hL.2 sx t qx fqx hOut).mp hqx
    have he := function_unique hF.1 hv' hv
    subst v'
    exact (hAssoc v gs fx fq gsx fqx (hF.2 t v hv) (hg.2 s gs hgs) (hf.2 x fx hx)
      hvgs (hEq s x sx gs fx gsx hProd hgs hx hgsx)).mpr hvgsx

def multiplicativeAt {m : Nat} (H mulN F q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ 4 q.succ.succ.succ.succ.succ 3)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ 4 2)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ
    1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ.succ 3 0))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ 2 1 0)))))))))))

theorem multiplicativeAt_freeClosed {m : Nat} (H mulN F q : Fin m) :
    (multiplicativeAt H mulN F q).FreeClosed := by
  simp -implicitDefEqProofs [multiplicativeAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem multiplicativeAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (H mulN F q : Fin m) :
    Project.Formula.satisfies env (multiplicativeAt H mulN F q) ↔ ∀ x xq fx fq fxq,
      Product (env.bound H) x (env.bound q) xq → PureKuratowski.PairMember M x fx (env.bound F) →
      PureKuratowski.PairMember M (env.bound q) fq (env.bound F) →
      PureKuratowski.PairMember M xq fxq (env.bound F) → Product (env.bound mulN) fx fq fxq := by
  simp only [multiplicativeAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

/-- Source evaluate_mul, by the existing object-formula induction on the
RIGHT internal word, preserving the literal source multiplication order. -/
theorem evaluate_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W N mulN f g F T H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D S W) (hF : MapsTo W N F) (hf : MapsTo D N f) (hg : MapsTo S N g)
    (hAssoc : Associative N mulN) (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hEq : Equivariant A f g mulN) (hTable : ActionTable w D S zero mul A T)
    (hProduct : ConstructionMergerWordProduct.Laws w D S zero T H)
    (hL : EvaluationLaws w D S zero mulN f g F) :
    ConstructionProbeLiftHom.PreservesProducts H mulN F := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    ⟨Fin.cases H (Fin.cases mulN (fun _ => F)),fun _ => w⟩
  let p : Project.UnarySchema 3 := { body := multiplicativeAt 1 2 3 0,freeClosed := multiplicativeAt_freeClosed .. }
  have he q : p.denote env q ↔ ∀ x xq fx fq fxq, Product H x q xq →
      PureKuratowski.PairMember M x fx F → PureKuratowski.PairMember M q fq F →
      PureKuratowski.PairMember M xq fxq F → Product mulN fx fq fxq :=
    multiplicativeAt_semantics hM (env.push q) 1 2 3 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro a q hOld
    apply (he q).mpr
    intro x xq fx fq fxq hProd hx hq hxq
    exact evaluate_act hF hf hg hAssoc hPres hEq hTable hL
      ((hProduct.1 a x q xq hOld).mp hProd) hx ((hL.1 a q fq hOld).mp hq) hxq) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro x xq fx fq fxq hProd hx hq hxq
    obtain ⟨xt,hxt,hConsOut⟩ := (hProduct.2 s t q x xq hCons).mp hProd
    obtain ⟨ft,gs,hft,hgs,hftgs⟩ := (hL.2 s t q fq hCons).mp hq
    obtain ⟨fxt,gs',hfxt,hgs',hfxtgs⟩ := (hL.2 s xt xq fxq hConsOut).mp hxq
    have eg := function_unique hg.1 hgs' hgs
    subst gs'
    have hIH := (he t).mp ih x xt fx ft fxt hxt hx hft hfxt
    exact (hAssoc fx ft gs fxt fq fxq (hF.2 x fx hx) (hF.2 t ft hft) (hg.2 s gs hgs)
      hIH hftgs).mp hfxtgs)
  intro x y z fx fy fz hProd hx hy hzv
  exact (he y).mp (hAll y ((hW y).mp (function_input hF.1 hy))) x z fx fy fz hProd hx hy hzv

/-- Uniqueness of actual internal graphs, using the existing agreement formula. -/
theorem evaluation_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero W N J mulN f g F K : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D S W) (hMul : MapsTo J N mulN) (hf : MapsTo D N f) (hg : MapsTo S N g)
    (hF : MapsTo W N F) (hK : MapsTo W N K)
    (hL : EvaluationLaws w D S zero mulN f g F) (hL' : EvaluationLaws w D S zero mulN f g K) : F = K := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := ⟨Fin.cases F (fun _ => K),fun _ => w⟩
  let p : Project.UnarySchema 2 := {
    body := ConstructionProbeHomExt.agreeAt 0 1 2,freeClosed := ConstructionProbeHomExt.agreeAt_freeClosed .. }
  have he q : p.denote env q ↔ ConstructionProbeHomExt.AgreeAt q F K :=
    ConstructionProbeHomExt.agreeAt_semantics hM (env.push q) 0 1 2
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro y z hy hzv
    exact function_unique hf.1 ((hL.1 x q y hOld).mp hy) ((hL'.1 x q z hOld).mp hzv)) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro y z hy hzv
    obtain ⟨v,gs,hv,hgs,hvy⟩ := (hL.2 s t q y hCons).mp hy
    obtain ⟨v',gs',hv',hgs',hvz⟩ := (hL'.2 s t q z hCons).mp hzv
    have ev := (he t).mp ih v v' hv hv'
    have es := function_unique hg.1 hgs hgs'
    subst v'; subst gs'
    exact product_unique hM hMul hvy hvz)
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM W N F).mp hF).1.1
    ((ForcingSupportSize.native_mapsTo hM W N K).mp hK).1.1
  intro q y
  constructor
  · intro hy
    have hq := function_input hF.1 hy
    obtain ⟨z,hzv,_⟩ := hK.1.2 q hq
    exact ((he q).mp (hAll q ((hW q).mp hq)) y z hy hzv).symm ▸ hzv
  · intro hy
    have hq := function_input hK.1 hy
    obtain ⟨z,hzv,_⟩ := hF.1.2 q hq
    exact ((he q).mp (hAll q ((hW q).mp hq)) z y hzv hy) ▸ hzv

/-- Agreement on the source old elements and literal single-letter words. -/
def Boundary (w D S zero unit f g F : M.Carrier .set) : Prop :=
  (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y F ↔ PureKuratowski.PairMember M x y f)) ∧
  ∀ s q y, Cons w D S s unit q → (PureKuratowski.PairMember M q y F ↔ PureKuratowski.PairMember M s y g)

theorem evaluation_boundary {w D S zero unit N mulN e eN f g F : M.Carrier .set}
    (hUnit : Old zero D e unit) (hf : MapsTo D N f) (hg : MapsTo S N g)
    (hOne : PureKuratowski.PairMember M e eN f) (hUN : Unit N mulN eN)
    (hL : EvaluationLaws w D S zero mulN f g F) : Boundary w D S zero unit f g F := by
  refine ⟨hL.1,?_⟩
  intro s q y hCons
  rw [hL.2 s unit q y hCons]
  constructor
  · rintro ⟨v,gs,hv,hgs,hProd⟩
    have ev := function_unique hf.1 ((hL.1 e unit v hUnit).mp hv) hOne
    subst v
    exact ((hUN.2 gs (hg.2 s gs hgs) y).1.mp hProd).symm ▸ hgs
  · intro hgs
    exact ⟨eN,y,(hL.1 e unit eN hUnit).mpr hOne,hgs,(hUN.2 y (hg.2 s y hgs) y).1.mpr rfl⟩

/-- Source hom_ext: every homomorphism with the specified boundary obeys
the literal snoc recurrence, via q = t * snoc(unit,s). -/
theorem hom_recurrence (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero W unit N J mulN eN f g F T H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hW : Carrier w D S W) (hUW : Unit W H unit)
    (hProduct : ConstructionMergerWordProduct.Laws w D S zero T H)
    (hMul : MapsTo J N mulN) (hg : MapsTo S N g)
    (hF : Hom W N H mulN unit eN F) (hB : Boundary w D S zero unit f g F) :
    EvaluationLaws w D S zero mulN f g F := by
  refine ⟨hB.1,?_⟩
  intro s t q y hCons
  have ht := (hW t).mpr (ConstructionProbeRaw.cons_raw hCons).1
  have hq := (hW q).mpr (ConstructionProbeRaw.cons_raw hCons).2
  have hs : (Project.FirstOrderSemantics.reduct M).mem s S := by
    rcases hCons with ⟨_,_,_,_,_,_,_,_,_,_,_,hs,_,_,_⟩
    exact hs
  obtain ⟨letter,hLetter⟩ := ConstructionProbeRaw.exists_cons hM hw hs ((hW unit).mp hUW.1)
  have hProd : Product H t letter q := (hProduct.2 s unit letter t q hLetter).mpr
    ⟨t,(hUW.2 t ht t).2.mpr rfl,hCons⟩
  constructor
  · intro hqy
    obtain ⟨v,hv,_⟩ := hF.1.1.2 t ht
    obtain ⟨gs,hgs,_⟩ := hg.1.2 s hs
    exact ⟨v,gs,hv,hgs,hF.2.2 t letter q v gs y hProd hv ((hB.2 s letter gs hLetter).mpr hgs) hqy⟩
  · rintro ⟨v,gs,hv,hgs,hProdN⟩
    obtain ⟨z,hzv,_⟩ := hF.1.1.2 q hq
    have hp := hF.2.2 t letter q v gs z hProd hv ((hB.2 s letter gs hLetter).mpr hgs) hzv
    exact (product_unique hM hMul hp hProdN) ▸ hzv

/-- Actual liftHom plus uniqueness among ALL internal monoid homomorphisms. -/
theorem existsUnique_lift (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e W T H unit N J mulN eN f g : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D S W) (hUnit : Old zero D e unit) (hUW : Unit W H unit)
    (hTable : ActionTable w D S zero mul A T)
    (hProduct : ConstructionMergerWordProduct.Laws w D S zero T H)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN)
    (hUN : Unit N mulN eN) (hAssoc : Associative N mulN)
    (hf : Hom D N mul mulN e eN f) (hg : MapsTo S N g) (hEq : Equivariant A f g mulN) :
    ∃ F, Hom W N H mulN unit eN F ∧ Boundary w D S zero unit f g F ∧
      ∀ K, Hom W N H mulN unit eN K → Boundary w D S zero unit f g K → K = F := by
  obtain ⟨F,hF,hL⟩ := exists_evaluation hM hw hz hzw hW hJ hMul hf.1 hg
  have hHom : Hom W N H mulN unit eN F := ⟨hF,(hL.1 e unit eN hUnit).mpr hf.2.1,
    evaluate_mul hM hw hz hzw hW hF hf.1 hg hAssoc hf.2.2 hEq hTable hProduct hL⟩
  have hB := evaluation_boundary hUnit hf.1 hg hf.2.1 hUN hL
  refine ⟨F,hHom,hB,?_⟩
  intro K hK hBK
  exact evaluation_unique hM hw hz hzw hW hMul hf.1 hg hK.1 hF
    (hom_recurrence hM hw hW hUW hProduct hMul hg hK hBK) hL

def equivariant {m : Nat} (A f g mulN : Fin m) : Project.Formula 1 m :=
    (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product A.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ.succ 2 1 0))))))))))))

theorem equivariant_freeClosed {m : Nat} (A f g mulN : Fin m) : (equivariant A f g mulN).FreeClosed := by
  simp -implicitDefEqProofs [equivariant,Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed]

theorem equivariant_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A f g mulN : Fin m) :
    Project.Formula.satisfies env (equivariant A f g mulN) ↔ Equivariant (env.bound A) (env.bound f) (env.bound g) (env.bound mulN) := by
  simp only [equivariant,Equivariant,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def boundary {m : Nat} (w D S zero unit f g F : Fin m) : Project.Formula 1 m :=
    (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ D.succ.succ.succ
    2 1) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 1 0)) (ProjectSyntax.encode
    id (Source.SetLanguage.edge f.succ.succ.succ 2 0))))))) (.forallE (.forallE (.forallE (.imp
    (ConstructionProbeRaw.cons w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 2 unit.succ.succ.succ 1)
    (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 1 0)) (ProjectSyntax.encode id
    (Source.SetLanguage.edge g.succ.succ.succ 2 0))))))))

theorem boundary_freeClosed {m : Nat} (w D S zero unit f g F : Fin m) : (boundary w D S zero unit f g F).FreeClosed := by
  simp -implicitDefEqProofs [boundary,Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,
    ConstructionProbeRaw.old_freeClosed,
    ConstructionProbeRaw.cons_freeClosed]

theorem boundary_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero unit f g F : Fin m) :
    Project.Formula.satisfies env (boundary w D S zero unit f g F) ↔ Boundary (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound unit) (env.bound f) (env.bound g) (env.bound F) := by
  simp only [boundary,Boundary,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_iff_iff,
    ConstructionProbeRaw.old_semantics hM,
    ConstructionProbeRaw.cons_semantics hM]
  rfl

def sourceSentence {m : Nat} (w D S zero mul A e W T H unit N J mulN eN f g : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem
    (.bound zero) (.bound w)) (.imp (ConstructionProbeRaw.carrier w D S W) (.imp (ConstructionProbeRaw.old
    zero D e unit) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit W H unit)) (.imp
    (ConstructionMergerWordAction.actionTable w D S zero mul A T) (.imp (ConstructionMergerWordProduct.laws w
    D S zero T H) (.imp (ConstructionProbeLetters.representatives N N J) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo mulN J N)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit N mulN eN))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.associative N mulN)) (.imp
    (ConstructionProbePushoutSyntax.hom D N mul mulN e eN f) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo g S N)) (.imp (equivariant A f g mulN) (.existsE (.conj
    (ConstructionProbePushoutSyntax.hom W.succ N.succ H.succ mulN.succ unit.succ eN.succ 0) (.conj (boundary
    w.succ D.succ S.succ zero.succ unit.succ f.succ g.succ 0) (.forallE (.imp
    (ConstructionProbePushoutSyntax.hom W.succ.succ N.succ.succ H.succ.succ mulN.succ.succ unit.succ.succ
    eN.succ.succ 0) (.imp (boundary w.succ.succ D.succ.succ S.succ.succ zero.succ.succ unit.succ.succ
    f.succ.succ g.succ.succ 0) (Project.Formula.extensionalEq (.bound 0) (.bound 1)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [
      Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isEmpty,
      ConstructionProbeRaw.carrier_freeClosed,
      ConstructionProbeRaw.old_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,
      ConstructionMergerWordProduct.laws_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      equivariant_freeClosed,
      boundary_freeClosed,
      Project.Formula.extensionalEq]

theorem source_models {m : Nat} (w D S zero mul A e W T H unit N J mulN eN f g : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w D S zero mul A e W T H unit N J mulN eN f g)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (sourceSentence w D S zero mul A e W T H unit N J mulN eN f g)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbeRaw.carrier_semantics hM,
    ConstructionProbeRaw.old_semantics hM,
    ConstructionMergerWordAction.actionTable_semantics hM,
    ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingDiagramPoset.unit_semantics (M := M),
    ForcingDiagramPoset.associative_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    equivariant_semantics hM,
    boundary_semantics hM]
  exact existsUnique_lift hM

theorem source_kernel_certificate {m : Nat} (w D S zero mul A e W T H unit N J mulN eN f g : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w D S zero mul A e W T H unit N J mulN eN f g)) :=
  ModelTransfer.derives (fun _ hM => source_models w D S zero mul A e W T H unit N J mulN eN f g hM)

end PPAC.Migration.ConstructionMergerEvaluation
