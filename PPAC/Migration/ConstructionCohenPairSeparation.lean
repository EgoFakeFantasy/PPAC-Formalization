/- Pinned StableSelectors.good_dense:188-199, the actual countable family
of unequal detector-site pairs and its simultaneous bit separation.
The previously proved fusion theorem receives a constructed set relation,
with persistence and density discharged by actual Cohen extensions. -/
import PPAC.Migration.ConstructionCohenSeparation

namespace PPAC.Migration.ConstructionCohenPairSeparation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Entry)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Pairs (J A : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z A ↔ ∃ j k,
    (Project.FirstOrderSemantics.reduct M).mem j J ∧ (Project.FirstOrderSemantics.reduct M).mem k J ∧
      j ≠ k ∧ PureKuratowski.Code M z j k

def Requirement (K lo hi z p : M.Carrier .set) : Prop := ∃ j k b,
  PureKuratowski.Code M z j k ∧ (Project.FirstOrderSemantics.reduct M).mem b K ∧
    Entry p j b lo ∧ Entry p k b hi

def requirement {m : Nat} (K lo hi z p : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.code (.bound z.succ.succ.succ) (.bound 2) (.bound 1))
    (.conj (.mem (.bound 0) (.bound K.succ.succ.succ))
      (.conj (ConstructionCohenCompatibility.entry p.succ.succ.succ 2 0 lo.succ.succ.succ)
        (ConstructionCohenCompatibility.entry p.succ.succ.succ 1 0 hi.succ.succ.succ))))))

theorem requirement_freeClosed {m : Nat} (K lo hi z p : Fin m) : (requirement K lo hi z p).FreeClosed := by
  simp -implicitDefEqProofs [requirement,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,
    ConstructionCohenCompatibility.entry_freeClosed]

theorem requirement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K lo hi z p : Fin m) :
    Project.Formula.satisfies env (requirement K lo hi z p) ↔
      Requirement (env.bound K) (env.bound lo) (env.bound hi) (env.bound z) (env.bound p) := by
  simp only [requirement,Requirement,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM,
    ConstructionCohenCompatibility.entry_semantics hM]
  rfl

theorem requirement_mono {K lo hi z p r : M.Carrier .set}
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset p r)
    (h : Requirement K lo hi z p) : Requirement K lo hi z r := by
  have lift {i k b : M.Carrier .set} (he : Entry p i k b) : Entry r i k b := by
    obtain ⟨a,ha,x,hx,hxp⟩ := he
    exact ⟨a,ha,x,hx,hSub x hxp⟩
  obtain ⟨j,k,b,hz,hb,hlo,hhi⟩ := h
  exact ⟨j,k,b,hz,hb,lift hlo,lift hhi⟩

theorem exists_pairs (hM : FirstOrder.Theory.Models M nativeZF)
    {w J : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hJ : Small J w) :
    ∃ A, Pairs J A ∧ Small A w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  obtain ⟨W,hW⟩ := ForcingCohenCoordinates.exists_cartesian hM J J
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hInf : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal P w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l P hZF hw,id,hId.1⟩
  have hSmall := (ForcingSupportSize.native_small hM W w).mpr
    (ExistingCardinalBounds.infinite_product_l P hZF hw hInf
      ((ForcingSupportSize.native_small hM J w).mp hJ) ((ForcingSupportSize.native_small hM J w).mp hJ) hW)
  let schema : Project.UnarySchema 0 := {
    body := .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))
      (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code,Project.Formula.extensionalEq] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := { bound := Fin.elim0, free := fun _ => J }
  have he z : schema.denote env z ↔ ∃ j k, PureKuratowski.Code M z j k ∧ j ≠ k := by
    simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
      KuratowskiZF.code_correct hM,Project.Term.eval_bound]
    rfl
  obtain ⟨A,hA⟩ := ZF.separation_exists_d hZF schema env W
  refine ⟨A,?_,ForcingSupportSize.small_subset hM (fun z hz => ((hA z).mp hz).1) hSmall⟩
  intro z
  constructor
  · intro hz
    obtain ⟨hzW,hzR⟩ := (hA z).mp hz
    obtain ⟨j,hj,k,hk,hz⟩ := (hW z).mp hzW
    obtain ⟨j',k',hz',hne⟩ := (he z).mp hzR
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
    exact ⟨j,k,hj,hk,hne,hz⟩
  · rintro ⟨j,k,hj,hk,hne,hz⟩
    exact (hA z).mpr ⟨(hW z).mpr ⟨j,hj,k,hk,hz⟩,(he z).mpr ⟨j,k,hz,hne⟩⟩

theorem exists_relation (hM : FirstOrder.Theory.Models M nativeZF) (K lo hi A P : M.Carrier .set) :
    ∃ R, ∀ z p, PureKuratowski.PairMember M z p R ↔
      (Project.FirstOrderSemantics.reduct M).mem z A ∧ (Project.FirstOrderSemantics.reduct M).mem p P ∧ Requirement K lo hi z p := by
  obtain ⟨W,hW⟩ := ForcingCohenCoordinates.exists_cartesian hM A P
  let schema : Project.UnarySchema 3 := {
    body := .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))
      (requirement 3 4 5 1 0)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code,requirement_freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases K (Fin.cases lo (fun _ => hi)), free := fun _ => A }
  have he e : schema.denote env e ↔ ∃ z p, PureKuratowski.Code M e z p ∧ Requirement K lo hi z p := by
    simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      KuratowskiZF.code_correct hM,Project.Term.eval_bound,requirement_semantics hM]
    rfl
  obtain ⟨R,hR⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env W
  refine ⟨R,?_⟩
  intro z p
  constructor
  · rintro ⟨e,hep,heR⟩
    obtain ⟨heW,heReq⟩ := (hR e).mp heR
    obtain ⟨z',hz,p',hp,hep'⟩ := (hW e).mp heW
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hep hep'
    obtain ⟨z',p',hep',hReq⟩ := (he e).mp heReq
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hep hep'
    exact ⟨hz,hp,hReq⟩
  · rintro ⟨hz,hp,hReq⟩
    obtain ⟨e,hep⟩ := KuratowskiZF.exists_code hM z p
    exact ⟨e,hep,(hR e).mpr ⟨(hW e).mpr ⟨z,hz,p,hp,hep⟩,(he e).mpr ⟨z,p,hep,hReq⟩⟩⟩

/-- The concrete source requirement relation is constructed, not assumed
persistent or dense. Every unequal pair of sites receives the prescribed
bits in one condition extending the original condition. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w I K C B S J p lo hi : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p) (hK : ¬ Small K w)
    (hJ : Small J w) (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I)
    (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B) :
    ∃ A r, Pairs J A ∧ Small A w ∧ Condition S w r ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
        ∀ z, (Project.FirstOrderSemantics.reduct M).mem z A → Requirement K lo hi z r := by
  obtain ⟨A,hA,hSmall⟩ := exists_pairs hM hw hJ
  obtain ⟨P,hP⟩ := ForcingCohenConditions.exists_carrier hM S w
  obtain ⟨R,hR⟩ := exists_relation hM K lo hi A P
  have hPersist : ConstructionCohenFusion.Persistent S w A R := by
    intro z hz q r _ hr hSub hReq
    exact (hR z r).mpr ⟨hz,(hP r).mpr hr,requirement_mono hSub ((hR z q).mp hReq).2.2⟩
  have hDense : ConstructionCohenFusion.Dense S w A R p := by
    intro z hz q hq _
    obtain ⟨j,k,hj,hk,hne,hzjk⟩ := (hA z).mp hz
    obtain ⟨r,a,hr,hqr,ha,hjlo,hkhi⟩ := ConstructionCohenSeparation.separate_labels hM hw hC hS hq hK
      (hJI j hj) (hJI k hk) hne hlo hhi
    exact ⟨r,hr,hqr,(hR z r).mpr ⟨hz,(hP r).mpr hr,j,k,a,hzjk,ha,hjlo,hkhi⟩⟩
  obtain ⟨r,hr,hpr,hReq⟩ := ConstructionCohenFusion.countable_fusion hM hChoice hw hSmall hp hPersist hDense
  exact ⟨A,r,hA,hSmall,hr,hpr,fun z hz => ((hR z r).mp (hReq z hz)).2.2⟩

def pairs {m : Nat} (J A : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound A.succ)) (.existsE (.existsE
    (.conj (.mem (.bound 1) (.bound J.succ.succ.succ))
      (.conj (.mem (.bound 0) (.bound J.succ.succ.succ))
        (.conj (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0)))
          (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))))))))

theorem pairs_freeClosed {m : Nat} (J A : Fin m) : (pairs J A).FreeClosed := by
  simp -implicitDefEqProofs [pairs,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,Project.Formula.extensionalEq]

theorem pairs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J A : Fin m) :
    Project.Formula.satisfies env (pairs J A) ↔ Pairs (env.bound J) (env.bound A) := by
  simp only [pairs,Pairs,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

def constructionSentence {m : Nat} (w I K C B S J p lo hi : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small K w))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small J w)) (.imp (Project.Formula.subset (.bound J) (.bound I)) (.imp (.mem (.bound lo) (.bound B)) (.imp (.mem (.bound hi) (.bound B)) (.existsE (.existsE (.conj (pairs J.succ.succ 1) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 1 w.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 0)) (.conj (Project.Formula.subset (.bound p.succ.succ) (.bound 0)) (.forallE (.imp (.mem (.bound 0) (.bound 2)) (requirement K.succ.succ.succ lo.succ.succ.succ hi.succ.succ.succ 0 1))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      Project.Formula.subset,pairs_freeClosed,requirement_freeClosed]

theorem construction_models {m : Nat} (w I K C B S J p lo hi : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w I K C B S J p lo hi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w I K C B S J p lo hi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),pairs_semantics hM,requirement_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w I K C B S J p lo hi : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w I K C B S J p lo hi))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w I K C B S J p lo hi)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w I K C B S J p lo hi)).mp (construction_models w I K C B S J p lo hi hL hChoice)



end PPAC.Migration.ConstructionCohenPairSeparation
