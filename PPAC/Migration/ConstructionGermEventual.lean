/- Pinned GermSelectors.eventualSetoid/Eventual/eventualMk/eventualMk_eq_iff:351-365.
Actual internal sequence space, equivalence classes and quotient projection.
The bound and all later indices range over internal omega, not host Nat.
Consumer: rawPattern:413 and StableSelectors.good_dense:207-219. -/
import PPAC.Migration.ConstructionFractionOrder

namespace PPAC.Migration.ConstructionGermEventual
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Same (w f g : M.Carrier .set) : Prop := ∃ N,
  (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ n,
    (Project.FirstOrderSemantics.reduct M).mem n w → NatLe N n → ∀ v,
      (PureKuratowski.PairMember M n v f ↔ PureKuratowski.PairMember M n v g)

def same {m : Nat} (w f g : Fin m) : Project.Formula 1 m := .existsE (.conj
  (.mem (.bound 0) (.bound w.succ)) (.forallE (.imp (.mem (.bound 0) (.bound w.succ.succ))
    (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0)))
      (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ 1 0))
        (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ.succ 1 0))))))))

theorem same_freeClosed {m : Nat} (w f g : Fin m) : (same w f g).FreeClosed := by
  simp -implicitDefEqProofs [same,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem same_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w f g : Fin m) :
    Project.Formula.satisfies env (same w f g) ↔ Same (env.bound w) (env.bound f) (env.bound g) := by
  simp only [same,Same,NatLe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem same_refl {w f : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) : Same w f f := by
  obtain ⟨z,_,hz⟩ := hw.1.1
  exact ⟨z,hz,fun _ _ _ _ => Iff.rfl⟩

theorem same_symm {w f g : M.Carrier .set} (h : Same w f g) : Same w g f := by
  obtain ⟨N,hN,h⟩ := h
  exact ⟨N,hN,fun n hn hNn v => (h n hn hNn v).symm⟩

theorem same_trans (hM : FirstOrder.Theory.Models M nativeZF) {w f g k : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hf : Same w f g) (hg : Same w g k) : Same w f k := by
  obtain ⟨N,hN,hf⟩ := hf
  obtain ⟨L,hL,hg⟩ := hg
  have compose {N L : M.Carrier .set} (hNL : NatLe N L) {n : M.Carrier .set}
      (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hLn : NatLe L n) : NatLe N n :=
    ZF.eqOrMem_trans (hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) n hn) hNL hLn
  rcases ConstructionFractionOrder.nat_compare hM hw hN hL with e | hNL | hLN
  · subst L
    exact ⟨N,hN,fun n hn hNn v => (hf n hn hNn v).trans (hg n hn hNn v)⟩
  · exact ⟨L,hL,fun n hn hLn v => (hf n hn (compose (Or.inr hNL) hn hLn) v).trans (hg n hn hLn v)⟩
  · exact ⟨N,hN,fun n hn hNn v => (hf n hn hNn v).trans (hg n hn (compose (Or.inr hLN) hn hNn) v)⟩

/-- On total internal sequences, graph-tail equality is exactly eventual value equality. -/
theorem same_iff_values {w A f g : M.Carrier .set} (hf : MapsTo w A f) (hg : MapsTo w A g) :
    Same w f g ↔ ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ n,
      (Project.FirstOrderSemantics.reduct M).mem n w → NatLe N n → ∀ x y,
        PureKuratowski.PairMember M n x f → PureKuratowski.PairMember M n y g → x = y := by
  constructor
  · rintro ⟨N,hN,h⟩
    exact ⟨N,hN,fun n hn hNn x y hx hy =>
      ForcingConditionGraphs.function_unique hg.1 ((h n hn hNn x).mp hx) hy⟩
  · rintro ⟨N,hN,h⟩
    refine ⟨N,hN,fun n hn hNn v => ⟨?_,?_⟩⟩
    · intro hv
      obtain ⟨y,hy,_⟩ := hg.1.2 n hn
      exact (h n hn hNn v y hv hy).symm ▸ hy
    · intro hv
      obtain ⟨x,hx,_⟩ := hf.1.2 n hn
      exact h n hn hNn x v hx hv ▸ hx

def Space (w A S : M.Carrier .set) : Prop := ∀ f,
  (Project.FirstOrderSemantics.reduct M).mem f S ↔ MapsTo w A f

def space {m : Nat} (w A S : Fin m) : Project.Formula 1 m := .forallE (.iff
  (.mem (.bound 0) (.bound S.succ)) (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 w.succ A.succ)))

theorem space_freeClosed {m : Nat} (w A S : Fin m) : (space w A S).FreeClosed := by
  simp -implicitDefEqProofs [space,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem space_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w A S : Fin m) :
    Project.Formula.satisfies env (space w A S) ↔ Space (env.bound w) (env.bound A) (env.bound S) := by
  simp only [space,Space,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def Class (w S f C : M.Carrier .set) : Prop := ∀ g,
  (Project.FirstOrderSemantics.reduct M).mem g C ↔ (Project.FirstOrderSemantics.reduct M).mem g S ∧ Same w f g

def eqClass {m : Nat} (w S f C : Fin m) : Project.Formula 1 m := .forallE (.iff
  (.mem (.bound 0) (.bound C.succ)) (.conj (.mem (.bound 0) (.bound S.succ)) (same w.succ f.succ 0)))

theorem eqClass_freeClosed {m : Nat} (w S f C : Fin m) : (eqClass w S f C).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,same_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w S f C : Fin m) :
    Project.Formula.satisfies env (eqClass w S f C) ↔ Class (env.bound w) (env.bound S) (env.bound f) (env.bound C) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,same_semantics hM]
  rfl

def Classes (w S Q : M.Carrier .set) : Prop := ∀ C,
  (Project.FirstOrderSemantics.reduct M).mem C Q ↔ ∃ f, (Project.FirstOrderSemantics.reduct M).mem f S ∧ Class w S f C

def classes {m : Nat} (w S Q : Fin m) : Project.Formula 1 m := .forallE (.iff
  (.mem (.bound 0) (.bound Q.succ)) (.existsE (.conj (.mem (.bound 0) (.bound S.succ.succ))
    (eqClass w.succ.succ S.succ.succ 0 1))))

theorem classes_freeClosed {m : Nat} (w S Q : Fin m) : (classes w S Q).FreeClosed := by
  simp -implicitDefEqProofs [classes,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem classes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w S Q : Fin m) :
    Project.Formula.satisfies env (classes w S Q) ↔ Classes (env.bound w) (env.bound S) (env.bound Q) := by
  simp only [classes,Classes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,eqClass_semantics hM]
  rfl

def Projection (w S pr : M.Carrier .set) : Prop := ∀ f C,
  PureKuratowski.PairMember M f C pr ↔ (Project.FirstOrderSemantics.reduct M).mem f S ∧ Class w S f C

def projection {m : Nat} (w S pr : Fin m) : Project.Formula 1 m := .forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ 1 0))
  (.conj (.mem (.bound 1) (.bound S.succ.succ)) (eqClass w.succ.succ S.succ.succ 1 0))))

theorem projection_freeClosed {m : Nat} (w S pr : Fin m) : (projection w S pr).FreeClosed := by
  simp -implicitDefEqProofs [projection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w S pr : Fin m) :
    Project.Formula.satisfies env (projection w S pr) ↔ Projection (env.bound w) (env.bound S) (env.bound pr) := by
  simp only [projection,Projection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,eqClass_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) (w S f : M.Carrier .set) : ∃ C, Class w S f C := by
  let schema : Project.UnarySchema 2 := { body := same 1 2 0, freeClosed := same_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases w (fun _ => f), free := fun _ => f }
  have he g : schema.denote env g ↔ Same w f g := same_semantics hM (env.push g) 1 2 0
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env S
  exact ⟨C,fun g => (hC g).trans (and_congr Iff.rfl (he g))⟩

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {w S f C E : M.Carrier .set}
    (hC : Class w S f C) (hE : Class w S f E) : C = E :=
  (ModelTransfer.extensionality hM).eq_of_same_members C E (fun g => (hC g).trans (hE g).symm)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {w S f g C E : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hg : (Project.FirstOrderSemantics.reduct M).mem g S)
    (hC : Class w S f C) (hE : Class w S g E) : C = E ↔ Same w f g := by
  constructor
  · rintro rfl
    exact ((hC g).mp ((hE g).mpr ⟨hg,same_refl hw⟩)).2
  · intro h
    apply (ModelTransfer.extensionality hM).eq_of_same_members C E
    intro k
    rw [hC k,hE k]
    exact and_congr_right (fun _ => ⟨fun hf => same_trans hM hw (same_symm h) hf,
      fun hg => same_trans hM hw h hg⟩)

theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF) (w S : M.Carrier .set) :
    ∃ Q pr, MapsTo S Q pr ∧ Classes w S Q ∧ Projection w S pr := by
  let schema : Project.BinarySchema 2 := { body := eqClass 2 3 1 0, freeClosed := eqClass_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases w (fun _ => S), free := fun _ => S }
  have he f C : schema.denote env f C ↔ Class w S f C := eqClass_semantics hM ((env.push f).push C) 2 3 1 0
  have ht : ∀ f, (Project.FirstOrderSemantics.reduct M).mem f S → ∃ C, schema.denote env f C := by
    intro f _
    obtain ⟨C,hC⟩ := exists_class hM w S f
    exact ⟨C,(he f C).mpr hC⟩
  have hu : ∀ f C E, schema.denote env f C → schema.denote env f E → C = E :=
    fun f C E hC hE => class_unique hM ((he f C).mp hC) ((he f E).mp hE)
  obtain ⟨Q,hQ⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env S ht hu
  obtain ⟨pr,hpr,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun f _ C E hC hE => hu f C E hC hE)
    (fun f C hf hC => (hQ C).mpr ⟨f,hf,hC⟩)
  refine ⟨Q,pr,(ForcingSupportSize.native_mapsTo hM S Q pr).mpr hpr,?_,?_⟩
  · exact fun C => (hQ C).trans ⟨fun ⟨f,hf,hC⟩ => ⟨f,hf,(he f C).mp hC⟩,
      fun ⟨f,hf,hC⟩ => ⟨f,hf,(he f C).mpr hC⟩⟩
  · exact fun f C => (hEdge f C).trans (and_congr Iff.rfl (he f C))

def Exact (w pr : M.Carrier .set) : Prop := ∀ f g C E,
  PureKuratowski.PairMember M f C pr → PureKuratowski.PairMember M g E pr → (C = E ↔ Same w f g)

def exactProjection {m : Nat} (w pr : Fin m) : Project.Formula 1 m := .forallE (.forallE (.forallE (.forallE
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ.succ 3 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ.succ 2 0))
      (.iff (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (same w.succ.succ.succ.succ 3 2)))))))

theorem exactProjection_freeClosed {m : Nat} (w pr : Fin m) : (exactProjection w pr).FreeClosed := by
  simp -implicitDefEqProofs [exactProjection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,same_freeClosed]

theorem exactProjection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w pr : Fin m) :
    Project.Formula.satisfies env (exactProjection w pr) ↔ Exact (env.bound w) (env.bound pr) := by
  simp only [exactProjection,Exact,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    same_semantics hM,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem construction (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set} (A : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ S Q pr, Space w A S ∧ MapsTo S Q pr ∧ Classes w S Q ∧ Projection w S pr ∧ Exact w pr := by
  obtain ⟨S,hS⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) w A
  obtain ⟨Q,pr,hpr,hQ,hProjection⟩ := exists_quotient hM w S
  refine ⟨S,Q,pr,(fun f => (hS f).trans (ForcingSupportSize.native_mapsTo hM w A f).symm),hpr,hQ,hProjection,?_⟩
  intro f g C E hf hg
  exact class_eq_iff hM hw ((hProjection g E).mp hg).1 ((hProjection f C).mp hf).2 ((hProjection g E).mp hg).2

def constructionSentence {m : Nat} (w A : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
    (.existsE (.existsE (.existsE (.conj (space w.succ.succ.succ A.succ.succ.succ 2)
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1))
        (.conj (classes w.succ.succ.succ 2 1) (.conj (projection w.succ.succ.succ 2 0) (exactProjection w.succ.succ.succ 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,
      space_freeClosed,classes_freeClosed,projection_freeClosed,exactProjection_freeClosed]

theorem construction_models {m : Nat} (w A : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w A)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w A)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    space_semantics hM,classes_semantics hM,projection_semantics hM,exactProjection_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M)]
  exact construction hM _

theorem construction_kernel_certificate {m : Nat} (w A : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w A)) :=
  ModelTransfer.derives (fun _ hM => construction_models w A hM)

end PPAC.Migration.ConstructionGermEventual
