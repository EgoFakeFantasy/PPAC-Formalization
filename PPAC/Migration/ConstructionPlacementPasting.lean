/- Pinned DiagramPlacements.paste_placements:250 and extend_two_placements:286.
Retain BOTH exact intersections, pointwise fixed root, every prescribed edge
and freshness outside the WHOLE source union. Reuse the original native graph
constructor and already proved extend_permutation_off; no new graph backend. -/
import PPAC.Migration.ConstructionPlacementExtensions

namespace PPAC.Migration.ConstructionPlacementPasting
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
open ForcingConditionGraphs (Permutation)
open ForcingLabelPermutations (Fixes)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Union (U A B : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsUnionOfTwo U A B

def Intersection (A B root : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x root ↔
    (Project.FirstOrderSemantics.reduct M).mem x A ∧ (Project.FirstOrderSemantics.reduct M).mem x B

def ImageIntersection (a A b B root : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z root ↔
    (∃ x, (Project.FirstOrderSemantics.reduct M).mem x A ∧ PureKuratowski.PairMember M x z a) ∧
      (∃ y, (Project.FirstOrderSemantics.reduct M).mem y B ∧ PureKuratowski.PairMember M y z b)

/-- On S, every prescribed edge of a is an edge of p. For actual functions,
this is exactly the source pointwise equation p x = a x. -/
def AgreesOn (S p a : M.Carrier .set) : Prop :=
  ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x S →
    PureKuratowski.PairMember M x y a → PureKuratowski.PairMember M x y p

def Inputs (I A B root a b : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).MemberSubset A I ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset B I ∧
    Intersection A B root ∧ Permutation I a ∧ Permutation I b ∧
    Fixes root a ∧ Fixes root b ∧ ImageIntersection a A b B root

def Pasted (I A B a b U f : M.Carrier .set) : Prop :=
  Union U A B ∧ ForcingSupportSize.Injection U I f ∧ AgreesOn A f a ∧ AgreesOn B f b

def Extended (I A B v K a b U p : M.Carrier .set) : Prop :=
  Union U A B ∧ Permutation I p ∧ AgreesOn A p a ∧ AgreesOn B p b ∧
    ConstructionPlacementExtensions.Avoids K p v U

/-- The source hcross step, using the EXACT image intersection and root fixes. -/
theorem cross_eq {I A B root a b x y z : M.Carrier .set}
    (h : Inputs I A B root a b)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x A)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y B)
    (ha : PureKuratowski.PairMember M x z a) (hb : PureKuratowski.PairMember M y z b) : x = y := by
  obtain ⟨_,_,_,hpa,hpb,hfa,hfb,hImage⟩ := h
  have hz := (hImage z).mpr ⟨⟨x,hx,ha⟩,⟨y,hy,hb⟩⟩
  exact (hpa.2.1 x z z ha (hfa z hz)).trans (hpb.2.1 y z z hb (hfb z hz)).symm

theorem paste_placements (hM : FirstOrder.Theory.Models M nativeZF)
    {I A B root a b : M.Carrier .set} (h : Inputs I A B root a b) :
    ∃ U f, Pasted I A B a b U f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hInputs := h
  obtain ⟨hA,hB,hInter,ha,hb,hFixA,hFixB,_⟩ := h
  obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A B
  let schema : Project.BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound 3)))
      (.conj (.neg (.mem (.bound 1) (.bound 2)))
        (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound 4))) }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases A (Fin.cases a (fun _ => b)), free := fun _ => I }
  have hSchema x y : schema.denote env x y ↔
      ((Project.FirstOrderSemantics.reduct M).mem x A ∧ PureKuratowski.PairMember M x y a) ∨
        (¬ (Project.FirstOrderSemantics.reduct M).mem x A ∧ PureKuratowski.PairMember M x y b) := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_disj_iff,
      Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
      Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff pair]
    rfl
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF pair schema env
    (source := U) (target := I) (by
      intro x hx
      by_cases hxA : (Project.FirstOrderSemantics.reduct M).mem x A
      · obtain ⟨y,hxy,_⟩ := ha.1.1.2 x (hA x hxA)
        exact ⟨y,(hSchema x y).mpr (Or.inl ⟨hxA,hxy⟩)⟩
      · have hxB := ((hU x).mp hx).resolve_left hxA
        obtain ⟨y,hxy,_⟩ := hb.1.1.2 x (hB x hxB)
        exact ⟨y,(hSchema x y).mpr (Or.inr ⟨hxA,hxy⟩)⟩) (by
      intro x _ y z hy hz
      rcases (hSchema x y).mp hy with hy | hy <;> rcases (hSchema x z).mp hz with hz | hz
      · exact ForcingConditionGraphs.function_unique ha.1.1 hy.2 hz.2
      · exact False.elim (hz.1 hy.1)
      · exact False.elim (hy.1 hz.1)
      · exact ForcingConditionGraphs.function_unique hb.1.1 hy.2 hz.2) (by
      intro x y _ hy
      exact ((hSchema x y).mp hy).elim (fun h => ha.1.2 x y h.2) (fun h => hb.1.2 x y h.2))
  have hInjective : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo pair f U I := by
    refine ⟨hf,fun x y z hx hy => ?_⟩
    have hxU := ((he x z).mp hx).1
    have hyU := ((he y z).mp hy).1
    rcases (hSchema x z).mp ((he x z).mp hx).2 with hx | hx <;>
      rcases (hSchema y z).mp ((he y z).mp hy).2 with hy | hy
    · exact ha.2.1 x y z hx.2 hy.2
    · exact cross_eq hInputs hx.1 (((hU y).mp hyU).resolve_left hy.1) hx.2 hy.2
    · exact (cross_eq hInputs hy.1 (((hU x).mp hxU).resolve_left hx.1) hy.2 hx.2).symm
    · exact hb.2.1 x y z hx.2 hy.2
  have hAgreeA : AgreesOn A f a := by
    intro x y hx hxy
    exact (he x y).mpr ⟨(hU x).mpr (Or.inl hx),(hSchema x y).mpr (Or.inl ⟨hx,hxy⟩)⟩
  have hAgreeB : AgreesOn B f b := by
    intro x y hx hxy
    by_cases hxA : (Project.FirstOrderSemantics.reduct M).mem x A
    · have hp := (hInter x).mpr ⟨hxA,hx⟩
      have hy := ForcingConditionGraphs.function_unique hb.1.1 hxy (hFixB x hp)
      have haxy : PureKuratowski.PairMember M x y a := by simpa only [hy] using hFixA x hp
      exact hAgreeA x y hxA haxy
    · exact (he x y).mpr ⟨(hU x).mpr (Or.inr hx),(hSchema x y).mpr (Or.inr ⟨hxA,hxy⟩)⟩
  exact ⟨U,f,hU,(ForcingSupportSize.native_injection hM U I f).mpr hInjective,hAgreeA,hAgreeB⟩

theorem extend_two_placements (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu I A B root v K a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu) (h : Inputs I A B root a b)
    (hvSub : (Project.FirstOrderSemantics.reduct M).MemberSubset v I)
    (hKSub : (Project.FirstOrderSemantics.reduct M).MemberSubset K I)
    (hASmall : Small A mu) (hBSmall : Small B mu) (hv : Small v mu) (hK : Small K mu) :
    ∃ U p, Extended I A B v K a b U p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨U,f,hU,hf,hfa,hfb⟩ := paste_placements hM h
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset U I :=
    fun x hx => ((hU x).mp hx).elim (h.1 x) (h.2.1 x)
  have hSmall : Small U mu := (ForcingSupportSize.native_small hM U mu).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM A mu).mp hASmall)
      ((ForcingSupportSize.native_small hM B mu).mp hBSmall) hU)
  obtain ⟨p,hp,hExt,hAvoid⟩ := ConstructionPlacementExtensions.extend_permutation_off hM hChoice
    hw hMu hLarge hSub hvSub hKSub hSmall hv hK ((ForcingSupportSize.native_injection hM U I f).mp hf)
  exact ⟨U,p,hU,hp,fun x y hx haxy => hExt x y (hfa x y hx haxy),
    fun x y hx hbxy => hExt x y (hfb x y hx hbxy),hAvoid⟩

def unionF {m : Nat} (U A B : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound U.succ))
    (.disj (.mem (.bound 0) (.bound A.succ)) (.mem (.bound 0) (.bound B.succ))))

theorem unionF_freeClosed {m : Nat} (U A B : Fin m) : (unionF U A B).FreeClosed := by
  simp -implicitDefEqProofs [unionF,Definitional.Formula.FreeClosed]

theorem unionF_semantics {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (U A B : Fin m) :
    Project.Formula.satisfies env (unionF U A B) ↔ Union (env.bound U) (env.bound A) (env.bound B) := by
  simp only [unionF,Union,Structure.IsUnionOfTwo,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Term.eval_bound]
  rfl

def intersection {m : Nat} (A B root : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound root.succ))
    (.conj (.mem (.bound 0) (.bound A.succ)) (.mem (.bound 0) (.bound B.succ))))

theorem intersection_freeClosed {m : Nat} (A B root : Fin m) : (intersection A B root).FreeClosed := by
  simp -implicitDefEqProofs [intersection,Definitional.Formula.FreeClosed]

theorem intersection_semantics {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A B root : Fin m) :
    Project.Formula.satisfies env (intersection A B root) ↔
      Intersection (env.bound A) (env.bound B) (env.bound root) := by
  simp only [intersection,Intersection,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound]
  rfl

def imageIntersection {m : Nat} (a A b B root : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound root.succ))
    (.conj (.existsE (.conj (.mem (.bound 0) (.bound A.succ.succ))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 1) (.bound a.succ.succ))))
      (.existsE (.conj (.mem (.bound 0) (.bound B.succ.succ))
        (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 1) (.bound b.succ.succ))))))

theorem imageIntersection_freeClosed {m : Nat} (a A b B root : Fin m) :
    (imageIntersection a A b B root).FreeClosed := by
  simp -implicitDefEqProofs [imageIntersection,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed]

theorem imageIntersection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (a A b B root : Fin m) :
    Project.Formula.satisfies env (imageIntersection a A b B root) ↔
      ImageIntersection (env.bound a) (env.bound A) (env.bound b) (env.bound B) (env.bound root) := by
  simp only [imageIntersection,ImageIntersection,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def agreesOn {m : Nat} (S p a : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound S.succ.succ))
    (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound a.succ.succ))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound p.succ.succ)))))

theorem agreesOn_freeClosed {m : Nat} (S p a : Fin m) : (agreesOn S p a).FreeClosed := by
  simp -implicitDefEqProofs [agreesOn,Definitional.Formula.FreeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem agreesOn_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S p a : Fin m) :
    Project.Formula.satisfies env (agreesOn S p a) ↔
      AgreesOn (env.bound S) (env.bound p) (env.bound a) := by
  simp only [agreesOn,AgreesOn,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff
      (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def inputs {m : Nat} (I A B root a b : Fin m) : Project.Formula 1 m :=
  .conj (Project.Formula.subset (.bound A) (.bound I))
    (.conj (Project.Formula.subset (.bound B) (.bound I))
      (.conj (intersection A B root)
        (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I a))
          (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I b))
            (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixes root a))
              (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixes root b))
                (imageIntersection a A b B root)))))))

theorem inputs_freeClosed {m : Nat} (I A B root a b : Fin m) : (inputs I A B root a b).FreeClosed := by
  simp -implicitDefEqProofs [inputs,Definitional.Formula.FreeClosed,Project.Formula.subset,
    intersection_freeClosed,ProjectSyntax.freeClosed,imageIntersection_freeClosed]

theorem inputs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I A B root a b : Fin m) :
    Project.Formula.satisfies env (inputs I A B root a b) ↔
      Inputs (env.bound I) (env.bound A) (env.bound B) (env.bound root) (env.bound a) (env.bound b) := by
  simp only [inputs,Inputs,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    intersection_semantics,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingLabelPermutations.fixes_semantics (M := M),
    imageIntersection_semantics hM,Project.Term.eval_bound]
  rfl

def pasted {m : Nat} (I A B a b U f : Fin m) : Project.Formula 1 m :=
  .conj (unionF U A B) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection f U I))
    (.conj (agreesOn A f a) (agreesOn B f b)))

theorem pasted_freeClosed {m : Nat} (I A B a b U f : Fin m) : (pasted I A B a b U f).FreeClosed := by
  simp -implicitDefEqProofs [pasted,Definitional.Formula.FreeClosed,unionF_freeClosed,
    ProjectSyntax.freeClosed,agreesOn_freeClosed]

theorem pasted_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I A B a b U f : Fin m) :
    Project.Formula.satisfies env (pasted I A B a b U f) ↔
      Pasted (env.bound I) (env.bound A) (env.bound B) (env.bound a) (env.bound b) (env.bound U) (env.bound f) := by
  simp only [pasted,Pasted,Project.Formula.satisfies_conj_iff,unionF_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),agreesOn_semantics hM]
  rfl

def extended {m : Nat} (I A B v K a b U p : Fin m) : Project.Formula 1 m :=
  .conj (unionF U A B) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I p))
    (.conj (agreesOn A p a) (.conj (agreesOn B p b) (ConstructionPlacementExtensions.avoids K p v U))))

theorem extended_freeClosed {m : Nat} (I A B v K a b U p : Fin m) :
    (extended I A B v K a b U p).FreeClosed := by
  simp -implicitDefEqProofs [extended,Definitional.Formula.FreeClosed,unionF_freeClosed,
    ProjectSyntax.freeClosed,agreesOn_freeClosed,ConstructionPlacementExtensions.avoids_freeClosed]

theorem extended_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I A B v K a b U p : Fin m) :
    Project.Formula.satisfies env (extended I A B v K a b U p) ↔
      Extended (env.bound I) (env.bound A) (env.bound B) (env.bound v) (env.bound K)
        (env.bound a) (env.bound b) (env.bound U) (env.bound p) := by
  simp only [extended,Extended,Project.Formula.satisfies_conj_iff,unionF_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),agreesOn_semantics hM,
    ConstructionPlacementExtensions.avoids_semantics hM]
  rfl

def pasteSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6 (.imp (inputs 0 1 2 3 4 5)
    (.existsE (.existsE (pasted (0 : Fin 6).succ.succ (1 : Fin 6).succ.succ (2 : Fin 6).succ.succ
      (4 : Fin 6).succ.succ (5 : Fin 6).succ.succ 1 0))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,inputs_freeClosed,pasted_freeClosed]

theorem paste_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence pasteSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) pasteSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    inputs_semantics hM,pasted_semantics hM]
  exact fun h => paste_placements hM h

theorem paste_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence pasteSentence) :=
  ModelTransfer.derives (fun _ hM => paste_models hM)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 10))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 10)) (.bound (1 : Fin 10))) (.imp (.neg
    (ProjectSyntax.encode id (ForcingSupportSize.small (2 : Fin 10) 1))) (.imp (inputs (2 : Fin 10) 3 4
    5 8 9) (.imp (Project.Formula.subset (.bound (6 : Fin 10)) (.bound 2)) (.imp (Project.Formula.subset
    (.bound (7 : Fin 10)) (.bound 2)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (3 : Fin
    10) 1)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (4 : Fin 10) 1)) (.imp
    (ProjectSyntax.encode id (ForcingSupportSize.small (6 : Fin 10) 1)) (.imp (ProjectSyntax.encode id
    (ForcingSupportSize.small (7 : Fin 10) 1)) (.existsE (.existsE (extended (2 : Fin 10).succ.succ (3 :
    Fin 10).succ.succ (4 : Fin 10).succ.succ (6 : Fin 10).succ.succ (7 : Fin 10).succ.succ (8 : Fin
    10).succ.succ (9 : Fin 10).succ.succ 1 0)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed,inputs_freeClosed,
      Project.Formula.subset,extended_freeClosed]

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
    Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),inputs_semantics hM,
    Project.Formula.satisfies_subset_iff,extended_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hLarge h hvSub hKSub hA hB hv hK =>
    extend_two_placements hM hChoice hw hMu hLarge h hvSub hKSub hA hB hv hK

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

end PPAC.Migration.ConstructionPlacementPasting
