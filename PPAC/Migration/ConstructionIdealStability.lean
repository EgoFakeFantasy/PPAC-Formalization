/- Pinned GraphFusion.HeightCost.dense_stable_ideal:420-465, specialized to
actual Cohen conditions for forcedAvailability_dense_stable:605 and
AssignedGraphs.graphRelation_onto:236. Reuse existing internal height/cost
approximation, indexed choice and countable closure; all omega indices remain
internal. No new recursion, real-number or forcing backend. -/
import PPAC.Migration.ConstructionCohenFusion
import PPAC.Migration.ConstructionIdealProbes

namespace PPAC.Migration.ConstructionIdealStability
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionIdealApproximation
open ConstructionIdealProbes (ConeIdeal)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeGates (divides_trans)
open ForcingCohenConditions (Condition)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- A set graph of all actual ideals; monotonicity uses Cohen extension. -/
def Family (S w D mul a F : M.Carrier .set) : Prop :=
  (∀ p, Condition S w p → ∃ U, PureKuratowski.PairMember M p U F) ∧
  (∀ p U, Condition S w p → PureKuratowski.PairMember M p U F → ConeIdeal D mul a U) ∧
  ∀ p q U V, Condition S w p → Condition S w q → Subset p q →
    PureKuratowski.PairMember M p U F → PureKuratowski.PairMember M q V F → Subset U V

private def Future (S w D F p V : M.Carrier .set) : Prop := ∀ x,
  (Project.FirstOrderSemantics.reduct M).mem x V ↔
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ ∃ r U,
      Condition S w r ∧ Subset p r ∧ PureKuratowski.PairMember M r U F ∧
        (Project.FirstOrderSemantics.reduct M).mem x U

private def Step (hM : FirstOrder.Theory.Models M nativeZF)
    (S w Q D H F i p r : M.Carrier .set) : Prop :=
  Subset p r ∧ ∃ V s U z, Future S w D F p V ∧ Supremum V H s ∧
    PureKuratowski.PairMember M r U F ∧ (Project.FirstOrderSemantics.reduct M).mem z U ∧
      Approximates hM w Q H s i z

def family {m : Nat} (S w D mul a F : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ (0 : Fin (m+1)))) (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))))) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ (1 : Fin (m+2)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (ConstructionIdealProbes.coneIdeal D.succ.succ mul.succ.succ a.succ.succ (0 : Fin (m+2))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ.succ w.succ.succ.succ.succ (3 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ.succ w.succ.succ.succ.succ (2 : Fin (m+4)))) (.imp (Project.Formula.subset (.bound (3 : Fin (m+4))) (.bound (2 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))) (Project.Formula.subset (.bound (1 : Fin (m+4))) (.bound (0 : Fin (m+4)))))))))))))))

theorem family_freeClosed {m : Nat} (S w D mul a F : Fin m) :
    (family S w D mul a F).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,ConstructionIdealProbes.coneIdeal_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w D mul a F : Fin m) :
    Project.Formula.satisfies env (family S w D mul a F) ↔
      Family (env.bound S) (env.bound w) (env.bound D) (env.bound mul) (env.bound a) (env.bound F) := by
  simp only [family,Family,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingCohenConditions.condition_semantics (M := M),ConstructionIdealProbes.coneIdeal_semantics hM]
  rfl

private def future {m : Nat} (S w D F p V : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound V.succ)) (.conj (.mem (.bound (0 : Fin (m+1))) (.bound D.succ)) (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ (1 : Fin (m+3)))) (.conj (Project.Formula.subset (.bound p.succ.succ.succ) (.bound (1 : Fin (m+3)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))) (.mem (.bound (2 : Fin (m+3))) (.bound (0 : Fin (m+3))))))))))))

private theorem future_freeClosed {m : Nat} (S w D F p V : Fin m) :
    (future S w D F p V).FreeClosed := by
  simp -implicitDefEqProofs [future,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset]

private theorem future_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w D F p V : Fin m) :
    Project.Formula.satisfies env (future S w D F p V) ↔
      Future (env.bound S) (env.bound w) (env.bound D) (env.bound F) (env.bound p) (env.bound V) := by
  simp only [future,Future,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingCohenConditions.condition_semantics (M := M)]
  rfl

private def heightSup {m : Nat} (V H s : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound s.succ)) (.existsE (.existsE (.conj (.mem (.bound (1 : Fin (m+3))) (.bound V.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))) (.mem (.bound (2 : Fin (m+3))) (.bound (0 : Fin (m+3))))))))))

private theorem heightSup_freeClosed {m : Nat} (V H s : Fin m) :
    (heightSup V H s).FreeClosed := by
  simp -implicitDefEqProofs [heightSup,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

private theorem heightSup_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V H s : Fin m) :
    Project.Formula.satisfies env (heightSup V H s) ↔
      Supremum (env.bound V) (env.bound H) (env.bound s) := by
  simp only [heightSup,Supremum,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

private def step {m : Nat} (S w Q D H F i p r : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.subset (.bound p) (.bound r)) (.existsE (.existsE (.existsE (.existsE (.conj (future S.succ.succ.succ.succ w.succ.succ.succ.succ D.succ.succ.succ.succ F.succ.succ.succ.succ p.succ.succ.succ.succ (3 : Fin (m+4))) (.conj (heightSup (3 : Fin (m+4)) H.succ.succ.succ.succ (2 : Fin (m+4))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ r.succ.succ.succ.succ (1 : Fin (m+4)))) (.conj (.mem (.bound (0 : Fin (m+4))) (.bound (1 : Fin (m+4)))) (ConstructionIdealApproximation.approximates w.succ.succ.succ.succ Q.succ.succ.succ.succ H.succ.succ.succ.succ (2 : Fin (m+4)) i.succ.succ.succ.succ (0 : Fin (m+4))))))))))))

private theorem step_freeClosed {m : Nat} (S w Q D H F i p r : Fin m) :
    (step S w Q D H F i p r).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,future_freeClosed,heightSup_freeClosed,approximates_freeClosed]

private theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w Q D H F i p r : Fin m) :
    Project.Formula.satisfies env (step S w Q D H F i p r) ↔
      Step hM (env.bound S) (env.bound w) (env.bound Q) (env.bound D) (env.bound H) (env.bound F) (env.bound i) (env.bound p) (env.bound r) := by
  simp only [step,Step,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,future_semantics hM,heightSup_semantics hM,approximates_semantics hM]
  rfl

private theorem future_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {S w D F p : M.Carrier .set} :
    ∃ V, Future S w D F p V := by
  let schema : Project.UnarySchema 4 := {
    body := .existsE (.existsE (.conj
      (ProjectSyntax.encode id (ForcingCohenConditions.condition (3 : Fin 7) 4 1))
      (.conj (Project.Formula.subset (.bound 6) (.bound 1))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 7) 1 0))
        (.mem (.bound 2) (.bound 0))))))
    freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 :=
    { bound := Fin.cases S (Fin.cases w (Fin.cases F (fun _ => p))), free := fun _ => D }
  obtain ⟨V,hV⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env D
  refine ⟨V,?_⟩
  intro x
  have hs : schema.denote env x ↔ ∃ r U, Condition S w r ∧ Subset p r ∧
      PureKuratowski.PairMember M r U F ∧ (Project.FirstOrderSemantics.reduct M).mem x U := by
    simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
      Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
      ForcingCohenConditions.condition_semantics (M := M)]
    rfl
  exact (hV x).trans (and_congr_right (fun _ => hs))

/-- Literal source height-approximation recursion, on internal omega. -/
theorem dense_stable_ideal (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {S w Q R top D mul e mark H C a F p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hF : Family S w D mul a F) (hp : Condition S w p) :
    ∃ q, Condition S w q ∧ Subset p q ∧ ∀ r U V,
      Condition S w r → Subset q r → PureKuratowski.PairMember M q U F →
        PureKuratowski.PairMember M r V F → U = V := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨hm,hCon,hJ,_,_,hH,hBound,hC,hCost,hMargin,_,_⟩ := hObj
  obtain ⟨all,hAll⟩ := ForcingCohenConditions.exists_carrier hM S w
  let schema : Project.UnarySchema 8 := {
    body := step (3 : Fin 9) 4 5 6 7 8 2 1 0
    freeClosed := step_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 :=
    { bound := Fin.cases S (Fin.cases w (Fin.cases Q (Fin.cases D (Fin.cases H (fun _ => F))))),
      free := fun _ => D }
  have hStep i b c : schema.denote ((env.push i).push b) c ↔ Step hM S w Q D H F i b c := by
    exact step_semantics hM (((env.push i).push b).push c) 3 4 5 6 7 8 2 1 0
  obtain ⟨f,hNative,hZero,hNext⟩ := ExistingIndexedChoice.indexed_choice_l
    (KuratowskiZF.interpretation hM) (ConstructionDirectedCardinality.models_zfc hM hChoice)
    schema env hw ((hAll p).mpr hp) (by
      intro i b hi hb
      have hbC := (hAll b).mp hb
      obtain ⟨V,hV⟩ := future_exists hM (S := S) (w := w) (D := D) (F := F) (p := b)
      obtain ⟨s,hs,hSup⟩ := supremum_exists hM hR hTop hH hBound (U := V)
      obtain ⟨U,hbU⟩ := hF.1 b hbC
      have hU := hF.2.1 b U hbC hbU
      obtain ⟨x,hx⟩ := hU.2.2.1
      obtain ⟨height,hxh,_⟩ := hH.1.2 x (hU.1 x hx)
      obtain ⟨t,ht⟩ := (hBound x height hxh).1
      have hNonempty : ∃ t, (Project.FirstOrderSemantics.reduct M).mem t s :=
        ⟨t,(hSup t).mpr ⟨x,height,(hV x).mpr ⟨hU.1 x hx,b,U,hbC,fun _ h => h,hbU,hx⟩,hxh,ht⟩⟩
      obtain ⟨z,hz,hApprox⟩ := approximate hM hw hQ hR hH hs hSup hNonempty hi
      obtain ⟨_,c,U',hc,hbc,hcU,hzU⟩ := (hV z).mp hz
      exact ⟨c,(hAll c).mpr hc,(hStep i b c).mpr ⟨hbc,V,s,U',z,hV,hSup,hcU,hzU,hApprox⟩⟩)
  have hMaps := (ForcingSupportSize.native_mapsTo hM w all f).mpr hNative
  have hInc := ZF.cc_increasing_of_successor_l (KuratowskiZF.interpretation hM) hZF hw hNative
    (fun i j b c hij hib hjc => ((hStep i b c).mp (hNext i j b c hij hib hjc)).1)
  obtain ⟨q,hq,hBelow⟩ := ConstructionCohenFusion.countably_closed hM hChoice hw hMaps
    (fun c hc => (hAll c).mp hc) hInc
  obtain ⟨zero,hzero,_⟩ := hw.1.1
  refine ⟨q,hq,hBelow zero p (hZero zero hzero),?_⟩
  intro r U V hr hqr hqU hrV
  have hU := hF.2.1 q U hq hqU
  have hV := hF.2.1 r V hr hrV
  have hUV := hF.2.2 q r U V hq hr hqr hqU hrV
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro d
  constructor
  · exact hUV d
  · intro hd
    apply Classical.byContradiction
    intro hbad
    obtain ⟨cost,hdc,_⟩ := hC.1.2 d (hV.1 d hd)
    obtain ⟨i,n,one,unit,eps,hi,hni,hone,hunit,hEps,hEpsCost⟩ :=
      small_cost_step hM hw hQ ((hR cost).mp (hC.2 d cost hdc)) (hCost d cost hdc).1
    obtain ⟨j,hji,hjw⟩ := hw.1.2 i hi
    obtain ⟨b,hib,_⟩ := hMaps.1.2 i hi
    obtain ⟨c,hjc,_⟩ := hMaps.1.2 j hjw
    have hb := (hAll b).mp (hMaps.2 i b hib)
    have hc := (hAll c).mp (hMaps.2 j c hjc)
    obtain ⟨_,futureSet,s,Uc,z,hFuture,hSup,hcU,hzUc,hApprox⟩ :=
      (hStep i b c).mp (hNext i j b c hji hib hjc)
    have hzU := hF.2.2 c q Uc U hc hq (hBelow j c hjc) hcU hqU z hzUc
    have hzV := hUV z hzU
    have hnot : ¬ Divides D mul d z :=
      fun h => hbad (hU.2.2.2.2.1 d z (hV.1 d hd) hzU h)
    obtain ⟨out,hout,hzo,hdo⟩ := (ConstructionIdealProbes.directed hm hJ hV).2.2 z d hzV hd
    obtain ⟨nA,oneA,unitA,epsA,hz,total,hSucA,hOneA,hUnitA,hEpsA,hzH,hTotal,hApproxBound⟩ := hApprox
    have en := Structure.SuccessorOf.eq (ModelTransfer.extensionality hM) hSucA hni
    subst nA
    have eo := Structure.IsOrdinalOne.eq (ModelTransfer.extensionality hM) hOneA hone
    subst oneA
    have eu := KuratowskiZF.code_unique hM hUnitA.2.2.2 hunit.2.2.2
    subst unitA
    have ee := principal_unique hM hEpsA hEps
    subst epsA
    obtain ⟨height,houtH,_⟩ := hH.1.2 out (hV.1 out hout)
    have hnotBack : ¬ Divides D mul out z :=
      fun h => hnot (divides_trans hm (hV.1 d hd) hdo h)
    obtain ⟨cap,sum,_,hSum,hStrict,hMissed⟩ := hMargin z out hz height hzH houtH hzo hnotBack
    have hEpsCap : Subset eps cap := fun t ht =>
      hMissed d cost (hV.1 d hd) hdc hdo hnot t (hEpsCost t ht)
    have hMonoSum := ConstructionCutArithmetic.sum_mono hTotal hSum (fun _ h => h) hEpsCap
    have hFutureOut := (hFuture out).mpr
      ⟨hV.1 out hout,r,V,hr,fun t ht => hqr t (hBelow i b hib t ht),hrV,hout⟩
    exact hStrict.2 (fun t ht => hMonoSum t
      (hApproxBound t ((hSup t).mpr ⟨out,height,hFutureOut,houtH,ht⟩)))

def constructionSentence {m : Nat} (S w Q R top D mul e mark H C a F p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionFractionOrder.carrier w Q)
    (.imp (cutCarrier w Q R) (.imp (cut w Q top)
    (.imp (ConstructionRoundStepSyntax.objectFields w Q R top D mul e mark H C)
    (.imp (family S w D mul a F)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p))
      (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0))
      (.conj (Project.Formula.subset (.bound p.succ) (.bound 0))
      (.forallE (.forallE (.forallE
        (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ.succ w.succ.succ.succ.succ 2))
        (.imp (Project.Formula.subset (.bound 3) (.bound 2))
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ 3 1))
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ 2 0))
          (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      ConstructionFractionOrder.carrier_freeClosed,cutCarrier_freeClosed,cut_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,family_freeClosed,
      ProjectSyntax.freeClosed,Project.Formula.subset,Project.Formula.extensionalEq]

theorem construction_models {m : Nat} (S w Q R top D mul e mark H C a F p : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence S w Q R top D mul e mark H C a F p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,cutCarrier_semantics hM,cut_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,family_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingCohenConditions.condition_semantics (M := M)]
  exact dense_stable_ideal hM hChoice

/-- Original nativeZF kernel, in the SAME internal L; no ambient object Choice. -/
theorem construction_kernel_certificate {m : Nat} (S w Q R top D mul e mark H C a F p : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (ConstructibleGround.relative (constructionSentence S w Q R top D mul e mark H C a F p))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence S w Q R top D mul e mark H C a F p)
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL)
    (constructionSentence S w Q R top D mul e mark H C a F p)).mp
      (construction_models S w Q R top D mul e mark H C a F p hL hChoice)

end PPAC.Migration.ConstructionIdealStability
