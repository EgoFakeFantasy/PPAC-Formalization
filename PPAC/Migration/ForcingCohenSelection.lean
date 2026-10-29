/- Pinned OrdinalCodes.CohenSelection.lift/lift_coe/lift_covariance and
rank/orderType/fixed consumers. Lift inspects only the actual Cohen coordinate;
its covariance is derived from the existing full product action graph. -/
import PPAC.Migration.ForcingOrdinalRoot

namespace PPAC.Migration.ForcingCohenSelection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingSupportingRoot (Code code)
open ForcingCohenConditions (Condition)
open ForcingSupportSize (Injection)
open ForcingOrdinalFixed (Fixed FixedFamily)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source typed witnesses become actual internal condition/diagram predicates. -/
def Lift {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (D I S w a z : M.Carrier .set) : Prop :=
  ∃ d s, Condition S w d ∧ Injection D I s ∧ Code z d s ∧ MapRel R env a d

def lift {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (D I S w a z : Fin m) : Formula m :=
  let up : Fin m → Fin (m+2) := fun i => i.castSucc.castSucc
  let d := (Fin.last m).castSucc
  let s := Fin.last (m+1)
  .ex (.ex ((ForcingCohenConditions.condition (up S) (up w) d).conj
    ((Source.SetLanguage.injection s (up D) (up I)).conj
      ((code (up z) d s).conj (rel R (fun j => up (rp j)) (up a) d)))))

theorem lift_semantics {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (env : Fin m → M.Carrier .set) (D I S w a z : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (lift R rp D I S w a z) ↔
      Lift R (fun j => env (rp j)) (env D) (env I) (env S) (env w) (env a) (env z) := by
  simp only [lift,Lift,Formula.Realize,ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Relation consumed literally by existing ranks/collection, with shared parameters. -/
def liftRelation {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (D I S w : Fin m) : Formula (m+2) :=
  lift R (paramsUp (paramsUp rp)) D.castSucc.castSucc I.castSucc.castSucc
    S.castSucc.castSucc w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

theorem mapRel_lift {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (env : Fin m → M.Carrier .set) (D I S w : Fin m) (a z : M.Carrier .set) :
    MapRel (liftRelation R rp D I S w) env a z ↔
      Lift R (fun j => env (rp j)) (env D) (env I) (env S) (env w) a z := by
  unfold MapRel liftRelation
  rw [lift_semantics]
  simp only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem lift_coe {n : Nat} {R : Formula (n+2)} {env : Fin n → M.Carrier .set}
    {D I S w a z d s : M.Carrier .set} (hd : Condition S w d) (hs : Injection D I s)
    (hz : Code z d s) : Lift R env D I S w a z ↔ MapRel R env a d := by
  constructor
  · rintro ⟨e,t,_,_,⟨c,hc,hzc⟩,hR⟩
    obtain ⟨b,hb,hzb⟩ := hz
    have hcb := ForcingWithTopCarrier.single_injective hzc hzb
    subst b
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hb
    exact hR
  · exact fun hR => ⟨d,s,hd,hs,hz,hR⟩

/-- Source hR, with the already defined literal coordinate permutation. -/
def Covariant {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (S w H X : M.Carrier .set) : Prop :=
  ∀ pi a d q, (Project.FirstOrderSemantics.reduct M).mem pi H →
    (Project.FirstOrderSemantics.reduct M).mem a X → Condition S w d → Condition S w q →
    ConstructionCohenCompatibility.Moved pi d q → MapRel R env a d → MapRel R env a q

theorem lift_covariance (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I K B w H X pi act a z t : M.Carrier .set}
    (hpres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hR : Covariant R env (v 2) w H X)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (hact : MapRel actionFormula v pi act) (hzt : PureKuratowski.PairMember M z t act)
    (hz : Lift R env (v 0) I (v 2) w a z) : Lift R env (v 0) I (v 2) w a t := by
  obtain ⟨d,s,hd,_,⟨c,hc,hzc⟩,hRd⟩ := hz
  obtain ⟨f,g,ac,ad,r,hf,hfg,hg,hgg,_,hacg,_,hadg,_,hrg,_,hag⟩ :=
    (mapRel_action v pi act).mp hact
  rcases ((hag z t).mp hzt).2 with ⟨he,_⟩ | ⟨c',ct,hzc',htc,hcc⟩
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hzc he)
  · have hce := ForcingWithTopCarrier.single_injective hzc' hzc
    subst c'
    obtain ⟨d',s',q,u,hdsc,hdq,hsu,hqu⟩ := ((hrg c ct).mp hcc).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hdsc hc
    have hq := (hpres.2.2.1 q).mp ((hacg d' q).mp hdq).2.1
    have hu := (hpres.2.2.2.1 u).mp ((hadg s' u).mp hsu).2.1
    have him := ((hacg d' q).mp hdq).2.2
    have hMoved := ConstructionCohenCompatibility.moved_of_image hM hpres.1 hpres.2.1 hfg hgg hd him
    exact ⟨q,u,hq,hu,⟨ct,hqu,htc⟩,hR pi a d' q hpi ha hd hq hMoved hRd⟩

theorem lift_invariant (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (R : Formula (n+2)) (rp : Fin n → Fin m) (env : Fin m → M.Carrier .set)
    (ra : Fin 7 → Fin m) (I w : Fin m) {K B H X : M.Carrier .set}
    (hpres : Presentation (env (ra 0)) (env I) K B (env w) (env (ra 1)) (env (ra 2))
      (env (ra 3)) (env (ra 4)) (env (ra 5)) (env (ra 6)))
    (hR : Covariant R (fun j => env (rp j)) (env (ra 2)) (env w) H X) :
    ForcingOrdinalFixed.Invariant (liftRelation R rp (ra 0) I (ra 2) w) env
      (fun j => env (ra j)) H X := by
  intro pi act a z t hpi hact ha _ hzt hz
  exact (mapRel_lift R rp env (ra 0) I (ra 2) w a t).mpr
    (lift_covariance hM hpres hR hpi ha hact hzt
      ((mapRel_lift R rp env (ra 0) I (ra 2) w a z).mp hz))

/-- Source rank/orderType are the SAME existing rank graph and collected name. -/
theorem exists_fixed_ranks (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (R : Formula (n+2)) (rp : Fin n → Fin m) (env : Fin m → M.Carrier .set)
    (ra : Fin 7 → Fin m) (I w : Fin m) {K B G F H X order : M.Carrier .set}
    (hpres : Presentation (env (ra 0)) (env I) K B (env w) (env (ra 1)) (env (ra 2))
      (env (ra 3)) (env (ra 4)) (env (ra 5)) (env (ra 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) G) (hF : ForcingNormalFilter.Normal (env I) G F)
    (hH : ForcingConjugationGraph.Subgroup (env I) G H)
    (hHF : (Project.FirstOrderSemantics.reduct M).mem H F)
    (hR : Covariant R (fun j => env (rp j)) (env (ra 2)) (env w) H X)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X) :
    ∃ history selection,
      ForcingOrdinalRanks.Ranks (liftRelation R rp (ra 0) I (ra 2) w) env X order (env (ra 6)) history ∧
      ForcingCollectedName.Collected (liftRelation R rp (ra 0) I (ra 2) w) env X history (env (ra 6)) selection ∧
      FixedFamily (fun j => env (ra j)) G F H X history ∧ Fixed (fun j => env (ra j)) G F H selection :=
  ForcingOrdinalFixed.exists_fixed_ranks hM (liftRelation R rp (ra 0) I (ra 2) w) env
    (fun j => env (ra j)) hpres hG hF hH hHF (lift_invariant hM R rp env ra I w hpres hR) hOrder

def covariant {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (S w H X : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+4) := fun j => j.succ.succ.succ.succ
  .forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (.mem 3 (up H))) (.imp
    (ProjectSyntax.encode id (.mem 2 (up X))) (.imp
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (up S) (up w) 1)) (.imp
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (up S) (up w) 0)) (.imp
    (ConstructionCohenCompatibility.moved 3 1 0) (.imp
    (ProjectSyntax.encode id (rel R (fun j => up (rp j)) 2 1))
    (ProjectSyntax.encode id (rel R (fun j => up (rp j)) 2 0)))))))))))

theorem covariant_freeClosed {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (S w H X : Fin m) : (covariant R rp S w H X).FreeClosed := by
  simp -implicitDefEqProofs [covariant,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCohenCompatibility.moved_freeClosed]

theorem covariant_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (R : Formula (n+2)) (rp : Fin n → Fin m)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w H X : Fin m) :
    Project.Formula.satisfies env (covariant R rp S w H X) ↔
      Covariant R (fun j => env.bound (rp j)) (env.bound S) (env.bound w) (env.bound H) (env.bound X) := by
  simp only [covariant,Covariant,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Formula.Realize,
    ForcingCohenConditions.condition_semantics (M := M),ConstructionCohenCompatibility.moved_semantics hM,
    ForcingMapConditions.rel_semantics (M := M)]
  rfl

/-- Both the coe equation and derived covariance, not an assumed invariant. -/
def liftSentence {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w H X a z d s : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (ProjectSyntax.encode id (ForcingProductFamily.presentation (ra 0) I K B w (ra 1) (ra 2) (ra 3) (ra 4) (ra 5) (ra 6)))
    (.imp (covariant R rp (ra 2) w H X) (.conj
      (ProjectSyntax.encode id (ForcingOrdinalFixed.invariant (liftRelation R rp (ra 0) I (ra 2) w) id ra H X))
      (ProjectSyntax.encode id ((ForcingCohenConditions.condition (ra 2) w d).imp
        ((Source.SetLanguage.injection s (ra 0) I).imp ((code z d s).imp
          ((lift R rp (ra 0) I (ra 2) w a z).iff (rel R rp a d)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,covariant_freeClosed]

theorem lift_models {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w H X a z d s : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (liftSentence R rp ra I K B w H X a z d s)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),covariant_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingOrdinalFixed.invariant_semantics (M := M),
    Source.Formula.iff,Formula.Realize,ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    lift_semantics (M := M),ForcingMapConditions.rel_semantics (M := M)]
  intro hp hR
  refine ⟨lift_invariant hM R rp env ra I w hp hR,?_⟩
  intro hd hs hz
  have he := lift_coe (R := R) (env := fun j => env (rp j)) (a := env a) hd hs hz
  exact ⟨he.mp,he.mpr⟩

theorem lift_kernel_certificate {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w H X a z d s : Fin m) : FirstOrder.Derives nativeZF []
      (Project.fo_sentence (liftSentence R rp ra I K B w H X a z d s)) :=
  ModelTransfer.derives (fun _ hM => lift_models R rp ra I K B w H X a z d s hM)


def context {m : Nat} (ra : Fin 7 → Fin m) (I K B w G F H : Fin m) : Formula m :=
  (ForcingProductFamily.presentation (ra 0) I K B w (ra 1) (ra 2) (ra 3) (ra 4) (ra 5) (ra 6)).conj
    ((ForcingLabelPermutations.carrier I G).conj ((ForcingNormalFilter.normal I G F).conj
      ((ForcingConjugationGraph.subgroup I G H).conj (Formula.mem H F))))

/-- The generated graph and type, with the source Cohen predicate as input. -/
def constructionSentence {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X order : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (covariant R rp (ra 2) w H X) (.imp
    (ProjectSyntax.encode id (context ra I K B w G F H)) (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
    (.existsE (.existsE (.conj
      (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks (liftRelation R rp (ra 0) I (ra 2) w)
        (fun j => j.succ.succ) X.succ.succ order.succ.succ (ra 6).succ.succ 1)) (.conj
      (ProjectSyntax.encode id (ForcingCollectedName.collected (liftRelation R rp (ra 0) I (ra 2) w)
        (fun j => j.succ.succ) X.succ.succ 1 (ra 6).succ.succ 0)) (.conj
      (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily (fun j => (ra j).succ.succ)
        G.succ.succ F.succ.succ H.succ.succ X.succ.succ 1))
      (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed (fun j => (ra j).succ.succ)
        G.succ.succ F.succ.succ H.succ.succ 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,covariant_freeClosed]

theorem construction_models {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X order : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence R rp ra I K B w G F H X order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    covariant_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    context,Formula.Realize,ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics (M := M),ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M)]
  rintro hR ⟨hp,hG,hF,hH,hHF⟩ hOrder
  exact exists_fixed_ranks hM R rp env ra I w hp hG hF hH hHF hR hOrder

theorem construction_kernel_certificate {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F H X order : Fin m) : FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence R rp ra I K B w G F H X order)) :=
  ModelTransfer.derives (fun _ hM => construction_models R rp ra I K B w G F H X order hM)

end PPAC.Migration.ForcingCohenSelection
