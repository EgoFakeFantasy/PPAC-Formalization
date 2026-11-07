/- Fixed OrdinalChoice.ChoiceFamily and forces_ACwo_of_dense.
Keep the literal source function formulas and full internal ordinal/HS domain.
This logical bridge does not assume its dense choices are already constructed. -/
import PPAC.Migration.ForcingRootProbes

namespace PPAC.Migration.ForcingOrdinalChoice
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingClassEvaluation (Predicate)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The exact source auxiliary formula F(x) contains z. -/
def familyMember : Formula 3 := .ex ((Source.SetLanguage.edge 0 1 3).conj (.mem 2 3))

section Logic
variable (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
variable {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
variable {P p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
variable (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
include hM hpre hp

omit hp in
theorem forces_familyMember (F x z : M.Carrier .set) :
    Force R H env (args3 F x z) P p familyMember ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          ∃ y, Predicate H env y ∧ Force R H env (args3 F x y) P r (Source.SetLanguage.edge 0 1 2) ∧
            Forces false R env P z y r := by
  unfold familyMember
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,y,hy,hApp,hmem⟩ := h q hq hqp
    exact ⟨r,hr,hrq,y,hy,(ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 4) 1 3).mp hApp,hmem⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,y,hy,hApp,hmem⟩ := h q hq hqp
    exact ⟨r,hr,hrq,y,hy,(ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 4) 1 3).mpr hApp,hmem⟩

/-- The full source family graph formula; its ordinal/index hypothesis is not weakened. -/
theorem forces_nonemptyFamily (v : Fin n → M.Carrier .set) (F d : Fin n) :
    Force R H env v P p (Source.SetLanguage.nonemptyFamily F d) ↔
      Force R H env v P p (Source.SetLanguage.functionOn F d) ∧
      ∀ x, Predicate H env x → ∀ y, Predicate H env y →
        ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
          Forces false R env P x (v d) q →
          ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
            Force R H env (args3 (v F) x y) P r (Source.SetLanguage.edge 0 1 2) →
            ∀ s, (Project.FirstOrderSemantics.reduct M).mem s P → MapRel R env s r →
              ∃ t, (Project.FirstOrderSemantics.reduct M).mem t P ∧ MapRel R env t s ∧
                ∃ z, Predicate H env z ∧ Forces false R env P z y t := by
  rw [Source.SetLanguage.nonemptyFamily,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  have hfunc : Force R H env (fun i => v (args2 F d i)) P p (Source.SetLanguage.functionOn 0 1) ↔
      Force R H env v P p (Source.SetLanguage.functionOn F d) := by
    rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,
      Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp]
    rfl
  rw [hfunc]
  constructor
  · rintro ⟨hf,hh⟩
    refine ⟨hf,?_⟩
    intro x hx y hy q hq hqp hxd r hr hrq hApp
    have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh x hx
    have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh y hy
    have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxd
    have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh r hr hrq
      ((ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 4) 2 3).mpr hApp)
    exact (ForcingChoiceFailure.forces_nonempty hM hpre hr _ _).mp hh
  · rintro ⟨hf,hh⟩
    refine ⟨hf,(ForcingFormula.force_all hM hpre hp _ _).mpr ?_⟩
    intro x hx
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro y hy
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hxd
    apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr hrq hApp
    apply (ForcingChoiceFailure.forces_nonempty hM hpre hr _ _).mpr
    exact hh x hx y hy q hq hqp hxd r hr hrq
      ((ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 4) 2 3).mp hApp)

/-- Complete choiceForFamily including full internal functionOn and actual membership. -/
theorem forces_choiceForFamily (v : Fin n → M.Carrier .set) (c d F : Fin n) :
    Force R H env v P p (Source.SetLanguage.choiceForFamily c d F) ↔
      Force R H env v P p (Source.SetLanguage.functionOn c d) ∧
      ∀ x, Predicate H env x → ∀ y, Predicate H env y →
        ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → Forces false R env P x (v d) q →
          ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
            Force R H env (args3 (v F) x y) P r (Source.SetLanguage.edge 0 1 2) →
            ∀ s, (Project.FirstOrderSemantics.reduct M).mem s P → MapRel R env s r →
              ∃ t, (Project.FirstOrderSemantics.reduct M).mem t P ∧ MapRel R env t s ∧
                ∃ z, Predicate H env z ∧ Force R H env (args3 (v c) x z) P t (Source.SetLanguage.edge 0 1 2) ∧
                  Forces false R env P z y t := by
  rw [Source.SetLanguage.choiceForFamily,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  have hfunc : Force R H env (fun i => v (args3 c d F i)) P p (Source.SetLanguage.functionOn 0 1) ↔
      Force R H env v P p (Source.SetLanguage.functionOn c d) := by
    rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,
      Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp]
    rfl
  rw [hfunc]
  constructor
  · rintro ⟨hf,hh⟩
    refine ⟨hf,?_⟩
    intro x hx y hy q hq hqp hxd r hr hrq hApp s hs hsr
    have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh x hx
    have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh y hy
    have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxd
    have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh r hr hrq
      ((ForcingRelationClass.edge_formula hM hpre hr _ (2 : Fin 5) 3 4).mpr hApp)
    obtain ⟨t,ht,hts,z,hz,hAppC,hmem⟩ := hh s hs hsr
    exact ⟨t,ht,hts,z,hz,(ForcingRelationClass.edge_formula hM hpre ht _ (0 : Fin 6) 3 5).mp hAppC,hmem⟩
  · rintro ⟨hf,hh⟩
    refine ⟨hf,(ForcingFormula.force_all hM hpre hp _ _).mpr ?_⟩
    intro x hx
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro y hy
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hxd
    apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr hrq hApp s hs hsr
    obtain ⟨t,ht,hts,z,hz,hAppC,hmem⟩ := hh x hx y hy q hq hqp hxd r hr hrq
      ((ForcingRelationClass.edge_formula hM hpre hr _ (2 : Fin 5) 3 4).mp hApp) s hs hsr
    exact ⟨t,ht,hts,z,hz,(ForcingRelationClass.edge_formula hM hpre ht _ (0 : Fin 6) 3 5).mpr hAppC,hmem⟩

theorem nonemptyFamily_member (v : Fin n → M.Carrier .set) (F d : Fin n)
    (hf : Force R H env v P p (Source.SetLanguage.nonemptyFamily F d))
    {x : M.Carrier .set} (hx : Predicate H env x) (hxd : Forces false R env P x (v d) p) :
    Force R H env (args2 (v F) x) P p familyMember.ex := by
  have hf := (forces_nonemptyFamily hM hpre hp v F d).mp hf
  intro q hq hqp
  obtain ⟨r,hr,hrq,y,hy,hApp,_⟩ := ForcingChoiceFailure.functionOn_total hM hpre hp v F d hf.1 hx hp (hpre.1 p hp) hxd hq hqp
  have hrp := hpre.2 r q p hr hq hp hrq hqp
  obtain ⟨s,hs,hsr,z,hz,hmem⟩ := hf.2 x hx y hy p hp (hpre.1 p hp) hxd r hr hrp hApp r hr (hpre.1 r hr)
  refine ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,z,hz,?_⟩
  have hvec : (Fin.lastCases z (args2 (v F) x) : Fin 3 → M.Carrier .set) = args3 (v F) x z := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rw [hvec]
  apply (forces_familyMember hM hpre (v F) x z).mpr
  intro t ht hts
  exact ⟨t,ht,hpre.1 t ht,y,hy,ForcingFormula.mono hM hpre _ _ hr ht (hpre.2 t s r ht hs hr hts hsr) hApp,
    ForcingAtomicBasic.mem_mono hM hpre ht hts hmem⟩

theorem familyMember_mem (v : Fin n → M.Carrier .set) (F d : Fin n)
    (hf : Force R H env v P p (Source.SetLanguage.functionOn F d))
    {x y z : M.Carrier .set} (hx : Predicate H env x) (hy : Predicate H env y) (_hz : Predicate H env z)
    (hxd : Forces false R env P x (v d) p)
    (hApp : Force R H env (args3 (v F) x y) P p (Source.SetLanguage.edge 0 1 2))
    (hMember : Force R H env (args3 (v F) x z) P p familyMember) : Forces false R env P z y p := by
  apply ForcingAtomicBasic.mem_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,t,ht,hAppT,hzt⟩ := (forces_familyMember hM hpre (v F) x z).mp hMember q hq hqp
  have hrp := hpre.2 r q p hr hq hp hrq hqp
  have he := ForcingChoiceFailure.functionOn_unique hM hpre hr v F d
    (ForcingFormula.mono hM hpre _ _ hp hr hrp hf) hx ht hy (ForcingAtomicBasic.mem_mono hM hpre hr hrp hxd)
    hAppT (ForcingFormula.mono hM hpre _ _ hp hr hrp hApp)
  exact ⟨r,hr,hrq,(ForcingAtomicLaws.mem_congr_right hM hpre he).mp hzt⟩
end Logic
/-- Exact source dense-choice contract: all internal ordinal and family names. -/
def DenseChoice {k : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (P : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P →
    ∀ eta, Predicate H env eta → ∀ F, Predicate H env F →
      Force R H env (args1 eta) P p (Source.SetLanguage.ordinal 0) →
      Force R H env (args2 F eta) P p (Source.SetLanguage.nonemptyFamily 0 1) →
      ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel R env q p ∧
        ∃ c, Predicate H env c ∧ Force R H env (args3 c eta F) P q (Source.SetLanguage.choiceForFamily 0 1 2)

/-- Fixed source forces_ACwo_of_dense. The dense hypothesis remains explicit
here and must be constructed by localized maximum/ground-family consumers. -/
theorem forces_ACwo_of_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P) (h : DenseChoice R H env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) : Force R H env Fin.elim0 P p Source.SetLanguage.ACwo := by
  rw [Source.SetLanguage.ACwo]
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro eta hEta
  apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
  intro q hq hqp ho
  apply (ForcingFormula.force_all hM hpre hq _ _).mpr
  intro F hF
  apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
  intro r hr hrq hf
  have hf' : Force R H env (args2 F eta) P r (Source.SetLanguage.nonemptyFamily 0 1) := by
    rw [Source.SetLanguage.nonemptyFamily,ForcingSound.rename hM hpre _ _ _ _ hr] at hf ⊢
    exact hf
  intro s hs hsr
  obtain ⟨t,ht,hts,c,hc,hChoice⟩ := h s hs eta hEta F hF
    (ForcingFormula.mono hM hpre _ _ hq hs (hpre.2 s r q hs hr hq hsr hrq) ho)
    (ForcingFormula.mono hM hpre _ _ hr hs hsr hf')
  refine ⟨t,ht,hts,c,hc,?_⟩
  change Force R H env (Fin.lastCases c (Fin.lastCases F (Fin.lastCases eta Fin.elim0))) P t
    (Source.SetLanguage.choiceForFamily 2 0 1)
  rw [Source.SetLanguage.choiceForFamily,ForcingSound.rename hM hpre _ _ _ _ ht] at hChoice ⊢
  exact hChoice

/-- The converse checks that the logical bridge has not weakened ACwo. -/
theorem dense_of_forces_ACwo (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (h : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → Force R H env Fin.elim0 P p Source.SetLanguage.ACwo) :
    DenseChoice R H env P := by
  intro p hp eta hEta F hF ho hf
  have hh := h p hp
  rw [Source.SetLanguage.ACwo] at hh
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh eta hEta
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh p hp (hpre.1 p hp) ho
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh F hF
  have hf' : Force R H env (Fin.lastCases F (Fin.lastCases eta Fin.elim0)) P p (Source.SetLanguage.nonemptyFamily 1 0) := by
    rw [Source.SetLanguage.nonemptyFamily,ForcingSound.rename hM hpre _ _ _ _ hp] at hf ⊢
    exact hf
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh p hp (hpre.1 p hp) hf'
  obtain ⟨q,hq,hqp,c,hc,hChoice⟩ := hh p hp (hpre.1 p hp)
  refine ⟨q,hq,hqp,c,hc,?_⟩
  change Force R H env (Fin.lastCases c (Fin.lastCases F (Fin.lastCases eta Fin.elim0))) P q
    (Source.SetLanguage.choiceForFamily 2 0 1) at hChoice
  rw [Source.SetLanguage.choiceForFamily,ForcingSound.rename hM hpre _ _ _ _ hq] at hChoice ⊢
  exact hChoice

/-- The dense source contract as a native object formula, retaining all binders. -/
def denseChoice {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P : Fin m) : Project.Formula 1 m :=
  let up3 : Fin k → Fin (m+3) := fun j => (base j).succ.succ.succ
  let up4 : Fin k → Fin (m+4) := fun j => (base j).succ.succ.succ.succ
  let up5 : Fin k → Fin (m+5) := fun j => (base j).succ.succ.succ.succ.succ
  let out : Project.Formula 1 (m+3) := .existsE
    (.conj (.mem (.bound 0) (.bound P.succ.succ.succ.succ))
    (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel R up4 0 3))
      (.existsE (.conj (ProjectSyntax.encode id (MinimalPredicates.pred H up5 0))
        (ProjectSyntax.encode id (ForcingFormula.formula R H up5 (args3 0 3 2) P.succ.succ.succ.succ.succ 1
          (Source.SetLanguage.choiceForFamily 0 1 2)))))))
  .forallE (.imp (.mem (.bound 0) (.bound P.succ))
    (.forallE (.imp (ProjectSyntax.encode id (MinimalPredicates.pred H (fun j => (base j).succ.succ) 0))
      (.forallE (.imp (ProjectSyntax.encode id (MinimalPredicates.pred H up3 0))
        (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H up3 (args1 1) P.succ.succ.succ 2
          (Source.SetLanguage.ordinal 0)))
        (.imp (ProjectSyntax.encode id (ForcingFormula.formula R H up3 (args2 0 1) P.succ.succ.succ 2
          (Source.SetLanguage.nonemptyFamily 0 1))) out)))))))

def allACwo {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound P.succ))
    (ProjectSyntax.encode id (ForcingFormula.formula R H (fun j => (base j).succ) Fin.elim0 P.succ 0 Source.SetLanguage.ACwo)))

private theorem args1_map {n : Nat} (v : Fin n → M.Carrier .set) (a : Fin n) :
    (fun i => v (args1 a i)) = args1 (v a) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i
private theorem args2_map {n : Nat} (v : Fin n → M.Carrier .set) (a b : Fin n) :
    (fun i => v (args2 a b i)) = args2 (v a) (v b) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
private theorem args3_map {n : Nat} (v : Fin n → M.Carrier .set) (a b c : Fin n) :
    (fun i => v (args3 a b c i)) = args3 (v a) (v b) (v c) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

theorem denseChoice_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P : Fin m) :
    Project.Formula.satisfies env (denseChoice R H base P) ↔ DenseChoice R H (fun j => env.bound (base j)) (env.bound P) := by
  simp only [denseChoice,DenseChoice,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingClassEvaluation.predicate_semantics,
    ForcingFormula.formula_semantics,ForcingMapConditions.rel_semantics,Project.Term.eval_bound,args1_map,args2_map,args3_map,id_eq]
  rfl

theorem allACwo_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P : Fin m) :
    Project.Formula.satisfies env (allACwo R H base P) ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound P) →
        Force R H (fun j => env.bound (base j)) Fin.elim0 (env.bound P) p Source.SetLanguage.ACwo := by
  simp only [allACwo,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingFormula.formula_semantics,Project.Term.eval_bound,id_eq]
  rfl

/-- Original-kernel logical equivalence, not a supplied-choice existence claim. -/
def sentence {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingAtomicBasic.preorder R id P))
      (.iff (denseChoice R H id P) (allACwo R H id P)))
  freeClosed := by
    simp -implicitDefEqProofs [denseChoice,allACwo,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Project.fo_sentence (sentence R H P)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k := {bound := bound,free := free}
  change Project.Formula.satisfies env _
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingAtomicBasic.preorder_semantics,
    denseChoice_semantics hM,allACwo_semantics hM,id_eq]
  intro hpre
  exact ⟨fun h p hp => forces_ACwo_of_dense hM hpre h hp,fun h => dense_of_forces_ACwo hM hpre h⟩

theorem kernel_certificate {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence R H P)) := ModelTransfer.derives (fun _ hM => models R H P hM)

end PPAC.Migration.ForcingOrdinalChoice
