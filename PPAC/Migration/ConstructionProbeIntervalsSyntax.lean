/- Pure native-ZF certificates for the source probe interval recipe and
its pointwise use on the actual floor/target/exit/cost graphs. -/
import PPAC.Migration.ConstructionProbeLetterIntervals
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionProbeCostBoundsSyntax

namespace PPAC.Migration.ConstructionProbeIntervalsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeIntervals ConstructionProbeLetterIntervals
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def recipe {m : Nat} (w Q four floor target exit c offset delta bound : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionCutDifference.value w.succ.succ.succ.succ
  Q.succ.succ.succ.succ floor.succ.succ.succ.succ target.succ.succ.succ.succ (3 : Fin (m+4))) (.conj
  (ConstructionCutArithmeticSyntax.maxCut (3 : Fin (m+4)) c.succ.succ.succ.succ bound.succ.succ.succ.succ)
  (.conj (ConstructionCutDifference.value w.succ.succ.succ.succ Q.succ.succ.succ.succ
  floor.succ.succ.succ.succ exit.succ.succ.succ.succ (2 : Fin (m+4))) (.conj
  (ConstructionCutDifference.value w.succ.succ.succ.succ Q.succ.succ.succ.succ bound.succ.succ.succ.succ
  (2 : Fin (m+4)) (1 : Fin (m+4))) (.conj (ConstructionCutDivision.value w.succ.succ.succ.succ
  Q.succ.succ.succ.succ four.succ.succ.succ.succ (1 : Fin (m+4)) delta.succ.succ.succ.succ) (.conj
  (ConstructionCutAddition.sumCut w.succ.succ.succ.succ Q.succ.succ.succ.succ delta.succ.succ.succ.succ
  delta.succ.succ.succ.succ (0 : Fin (m+4))) (ConstructionCutAddition.sumCut w.succ.succ.succ.succ
  Q.succ.succ.succ.succ floor.succ.succ.succ.succ (0 : Fin (m+4)) offset.succ.succ.succ.succ)))))))))))

theorem recipe_freeClosed {m : Nat} (w Q four floor target exit c offset delta bound : Fin m) : (recipe w Q four floor target exit c offset delta bound).FreeClosed := by
  simp -implicitDefEqProofs
  [recipe,Definitional.Formula.FreeClosed,ConstructionCutDifference.value_freeClosed,ConstructionCutArithmeticSyntax.maxCut_freeClosed,ConstructionCutDivision.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem recipe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q four floor target exit c offset delta bound : Fin m) :
    Project.Formula.satisfies env (recipe w Q four floor target exit c offset delta bound) ↔
    Recipe hM (env.bound w) (env.bound Q) (env.bound four) (env.bound floor) (env.bound target) (env.bound
    exit) (env.bound c) (env.bound offset) (env.bound delta) (env.bound bound) := by
  simp only
  [recipe,Recipe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionCutDifference.value_semantics
  hM,ConstructionCutArithmeticSyntax.maxCut_semantics,ConstructionCutDivision.value_semantics
  hM,ConstructionCutAddition.sumCut_semantics hM]
  rfl

def interval {m : Nat} (w Q floor target exit c offset delta bound : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionRealCuts.cut w Q offset) (.conj (ConstructionRealCuts.cut w Q delta) (.conj
  (ConstructionRealCuts.cut w Q bound) (.conj (.existsE (.mem (.bound (0 : Fin (m+1))) (.bound
  delta.succ))) (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRealCuts.cut
  w.succ.succ.succ.succ Q.succ.succ.succ.succ (3 : Fin (m+4))) (.conj (ConstructionCutAddition.sumCut
  w.succ.succ.succ.succ Q.succ.succ.succ.succ floor.succ.succ.succ.succ (3 : Fin (m+4))
  target.succ.succ.succ.succ) (.conj (Project.Formula.subset (.bound (3 : Fin (m+4))) (.bound
  bound.succ.succ.succ.succ)) (.conj (Project.Formula.subset (.bound c.succ.succ.succ.succ) (.bound
  bound.succ.succ.succ.succ)) (.conj (ConstructionCutAddition.sumCut w.succ.succ.succ.succ
  Q.succ.succ.succ.succ floor.succ.succ.succ.succ delta.succ.succ.succ.succ (2 : Fin (m+4))) (.conj (.conj
  (Project.Formula.subset (.bound (2 : Fin (m+4))) (.bound offset.succ.succ.succ.succ)) (.neg
  (Project.Formula.subset (.bound offset.succ.succ.succ.succ) (.bound (2 : Fin (m+4)))))) (.conj
  (ConstructionCutAddition.sumCut w.succ.succ.succ.succ Q.succ.succ.succ.succ offset.succ.succ.succ.succ
  delta.succ.succ.succ.succ (1 : Fin (m+4))) (.conj (ConstructionCutAddition.sumCut w.succ.succ.succ.succ
  Q.succ.succ.succ.succ (1 : Fin (m+4)) bound.succ.succ.succ.succ (0 : Fin (m+4))) (.conj
  (Project.Formula.subset (.bound (0 : Fin (m+4))) (.bound exit.succ.succ.succ.succ)) (.neg
  (Project.Formula.subset (.bound exit.succ.succ.succ.succ) (.bound (0 : Fin (m+4))))))))))))))))))))))

theorem interval_freeClosed {m : Nat} (w Q floor target exit c offset delta bound : Fin m) : (interval w Q floor target exit c offset delta bound).FreeClosed := by
  simp -implicitDefEqProofs
  [interval,Definitional.Formula.FreeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem interval_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q floor target exit c offset delta bound : Fin m) :
    Project.Formula.satisfies env (interval w Q floor target exit c offset delta bound) ↔
    Interval hM (env.bound w) (env.bound Q) (env.bound floor) (env.bound target) (env.bound exit)
    (env.bound c) (env.bound offset) (env.bound delta) (env.bound bound) := by
  simp only [interval,Interval,Project.Formula.satisfies_conj_iff,ConstructionRealCuts.cut_semantics
  hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,ConstructionCutAddition.sumCut_semantics
  hM,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound]
  rfl

def missedBound {m : Nat} (D mul cost x y bound : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound D.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge cost.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ mul.succ.succ (1 : Fin (m+2))
  y.succ.succ)) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ
  mul.succ.succ (1 : Fin (m+2)) x.succ.succ))) (Project.Formula.subset (.bound (0 : Fin (m+2))) (.bound
  bound.succ.succ))))))))

theorem missedBound_freeClosed {m : Nat} (D mul cost x y bound : Fin m) : (missedBound D mul cost x y bound).FreeClosed := by
  simp -implicitDefEqProofs [missedBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem missedBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul cost x y bound : Fin m) :
    Project.Formula.satisfies env (missedBound D mul cost x y bound) ↔
    MissedBound (env.bound D) (env.bound mul) (env.bound cost) (env.bound x) (env.bound y) (env.bound
    bound) := by
  simp only
  [missedBound,MissedBound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M
  := M),Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

def uniformAt {m : Nat} (w Q D mul cost x y hx hy : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ConstructionRealCuts.cut w.succ.succ Q.succ.succ (1 : Fin (m+2))) (.conj
  (ConstructionCutAddition.sumCut w.succ.succ Q.succ.succ hx.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))
  (.conj (.conj (Project.Formula.subset (.bound (0 : Fin (m+2))) (.bound hy.succ.succ)) (.neg
  (Project.Formula.subset (.bound hy.succ.succ) (.bound (0 : Fin (m+2)))))) (missedBound D.succ.succ
  mul.succ.succ cost.succ.succ x.succ.succ y.succ.succ (1 : Fin (m+2))))))))

theorem uniformAt_freeClosed {m : Nat} (w Q D mul cost x y hx hy : Fin m) : (uniformAt w Q D mul cost x y hx hy).FreeClosed := by
  simp -implicitDefEqProofs
  [uniformAt,Definitional.Formula.FreeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed,missedBound_freeClosed]

theorem uniformAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D mul cost x y hx hy : Fin m) :
    Project.Formula.satisfies env (uniformAt w Q D mul cost x y hx hy) ↔
    UniformAt hM (env.bound w) (env.bound Q) (env.bound D) (env.bound mul) (env.bound cost) (env.bound x)
    (env.bound y) (env.bound hx) (env.bound hy) := by
  simp only
  [uniformAt,UniformAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionRealCuts.cut_semantics
  hM,ConstructionCutAddition.sumCut_semantics
  hM,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_neg_iff,missedBound_semantics
  hM,Project.Term.eval_bound]
  rfl

def uniformMargins {m : Nat} (w Q D mul H C : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ
  (3 : Fin (m+4)) (2 : Fin (m+4)))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ mul.succ.succ.succ.succ (2 : Fin (m+4)) (3 : Fin (m+4))))) (uniformAt
  w.succ.succ.succ.succ Q.succ.succ.succ.succ D.succ.succ.succ.succ mul.succ.succ.succ.succ
  C.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (1 : Fin (m+4)) (0 : Fin (m+4)))))))))))

theorem uniformMargins_freeClosed {m : Nat} (w Q D mul H C : Fin m) : (uniformMargins w Q D mul H C).FreeClosed := by
  simp -implicitDefEqProofs
  [uniformMargins,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,uniformAt_freeClosed]

theorem uniformMargins_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D mul H C : Fin m) :
    Project.Formula.satisfies env (uniformMargins w Q D mul H C) ↔
    UniformMargins hM (env.bound w) (env.bound Q) (env.bound D) (env.bound mul) (env.bound H) (env.bound
    C) := by
  simp only
  [uniformMargins,UniformMargins,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M
  := M),Project.Formula.satisfies_neg_iff,uniformAt_semantics hM]
  rfl

def outsideBound {m : Nat} (D mul S A cost s exit bound : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound D.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge cost.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ mul.succ.succ (1 : Fin (m+2))
  exit.succ.succ)) (.imp (.neg (ConstructionProbeAlphabet.inCone S.succ.succ
  A.succ.succ (1 : Fin (m+2)) s.succ.succ)) (Project.Formula.subset (.bound (0 : Fin (m+2))) (.bound
  bound.succ.succ))))))))

theorem outsideBound_freeClosed {m : Nat} (D mul S A cost s exit bound : Fin m) : (outsideBound D mul S A cost s exit bound).FreeClosed := by
  simp -implicitDefEqProofs [outsideBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.inCone_freeClosed]

theorem outsideBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul S A cost s exit bound : Fin m) :
    Project.Formula.satisfies env (outsideBound D mul S A cost s exit bound) ↔
    OutsideBound (env.bound D) (env.bound mul) (env.bound S) (env.bound A) (env.bound cost) (env.bound s)
    (env.bound exit) (env.bound bound) := by
  simp only
  [outsideBound,OutsideBound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M
  :=
  M),Project.Formula.satisfies_neg_iff,ConstructionProbeAlphabet.inCone_semantics hM,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 11))) (.imp (ConstructionFractionOrder.carrier (0 :
    Fin 11) (1 : Fin 11)) (.imp (ConstructionBaseWeights.digits (0 : Fin 11) (6 : Fin 11) (7 : Fin 11) (8
    : Fin 11)) (.imp (Project.Formula.isSuccessor (.bound (9 : Fin 11)) (.bound (8 : Fin 11))) (.imp (.mem
    (.bound (9 : Fin 11)) (.bound (0 : Fin 11))) (.imp (ConstructionRealCuts.cut (0 : Fin 11) (1 : Fin 11)
    (2 : Fin 11)) (.imp (ConstructionRealCuts.cut (0 : Fin 11) (1 : Fin 11) (3 : Fin 11)) (.imp
    (ConstructionRealCuts.cut (0 : Fin 11) (1 : Fin 11) (4 : Fin 11)) (.imp (ConstructionRealCuts.cut (0 :
    Fin 11) (1 : Fin 11) (5 : Fin 11)) (.imp (Project.Formula.subset (.bound (2 : Fin 11)) (.bound (3 :
    Fin 11))) (.imp (ConstructionCutAddition.sumCut (0 : Fin 11) (1 : Fin 11) (3 : Fin 11) (5 : Fin 11)
    (10 : Fin 11)) (.imp (.conj (Project.Formula.subset (.bound (10 : Fin 11)) (.bound (4 : Fin 11)))
    (.neg (Project.Formula.subset (.bound (4 : Fin 11)) (.bound (10 : Fin 11))))) (.existsE (.existsE
    (.existsE (.conj (recipe (0 : Fin 11).succ.succ.succ (1 : Fin 11).succ.succ.succ (9 : Fin
    11).succ.succ.succ (2 : Fin 11).succ.succ.succ (3 : Fin 11).succ.succ.succ (4 : Fin 11).succ.succ.succ
    (5 : Fin 11).succ.succ.succ (2 : Fin (11+3)) (1 : Fin (11+3)) (0 : Fin (11+3))) (.conj (interval (0 :
    Fin 11).succ.succ.succ (1 : Fin 11).succ.succ.succ (2 : Fin 11).succ.succ.succ (3 : Fin
    11).succ.succ.succ (4 : Fin 11).succ.succ.succ (5 : Fin 11).succ.succ.succ (2 : Fin (11+3)) (1 : Fin
    (11+3)) (0 : Fin (11+3))) (.forallE (.forallE (.forallE (.imp (recipe (0 : Fin
    11).succ.succ.succ.succ.succ.succ (1 : Fin 11).succ.succ.succ.succ.succ.succ (9 : Fin
    11).succ.succ.succ.succ.succ.succ (2 : Fin 11).succ.succ.succ.succ.succ.succ (3 : Fin
    11).succ.succ.succ.succ.succ.succ (4 : Fin 11).succ.succ.succ.succ.succ.succ (5 : Fin
    11).succ.succ.succ.succ.succ.succ (2 : Fin (11+6)) (1 : Fin (11+6)) (0 : Fin (11+6))) (.conj
    (Project.Formula.extensionalEq (.bound (2 : Fin (11+6))) (.bound (5 : Fin (11+6)))) (.conj
    (Project.Formula.extensionalEq (.bound (1 : Fin (11+6))) (.bound (4 : Fin (11+6))))
    (Project.Formula.extensionalEq (.bound (0 : Fin (11+6))) (.bound (3 : Fin
    (11+6)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs
    [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionBaseWeights.digits_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed,recipe_freeClosed,interval_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only
  [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics
  hM,ConstructionBaseWeights.digits_semantics,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_mem_iff,ConstructionRealCuts.cut_semantics
  hM,Project.Formula.satisfies_subset_iff,ConstructionCutAddition.sumCut_semantics
  hM,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,recipe_semantics
  hM,interval_semantics
  hM,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_extensionalEq_iff_eq
  (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  intro hw hQ hd hf hfw hFloor hTarget hExit hC hFT hTC hRoom
  obtain ⟨offset,delta,bound,hRecipe,hInterval⟩ := exists_interval hM hw hQ hd hf hfw hFloor hTarget hExit hC hFT hTC hRoom
  exact ⟨offset,delta,bound,hRecipe,hInterval,fun _ _ _ h => recipe_unique hM h hRecipe⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

def letterSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 24
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 24))) (.imp (ConstructionFractionOrder.carrier (0 :
    Fin 24) (1 : Fin 24)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 24) (1 : Fin 24) (2 : Fin 24))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (3 : Fin 24) (4 : Fin 24) (5 :
    Fin 24))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (3 : Fin 24) (4 : Fin 24) (5 :
    Fin 24))) (.imp (.mem (.bound (6 : Fin 24)) (.bound (3 : Fin 24))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (6 : Fin 24)) (.bound (5 : Fin 24)))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 24) (7 : Fin 24) (3 : Fin 24))) (.imp
    (ConstructionProbeAlphabet.exitGraph (4 : Fin 24) (9 : Fin 24) (6 : Fin 24) (10 : Fin 24)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 24) (3 : Fin 24) (2 : Fin 24))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 24) (3 : Fin 24) (2 : Fin 24))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 24) (7 : Fin 24) (2 : Fin 24))) (.imp
    (ConstructionProbeLetterFloorSyntax.floorLaws (3 : Fin 24) (7 : Fin 24) (8 : Fin 24) (9 : Fin 24) (11
    : Fin 24) (13 : Fin 24)) (.imp (ConstructionProbeCostBoundsSyntax.costBounds (0 : Fin 24) (1 : Fin 24)
    (3 : Fin 24) (4 : Fin 24) (7 : Fin 24) (8 : Fin 24) (9 : Fin 24) (11 : Fin 24) (12 : Fin 24) (13 : Fin
    24)) (.imp (uniformMargins (0 : Fin 24) (1 : Fin 24) (3 : Fin 24) (4 : Fin 24) (11 : Fin 24) (12 : Fin
    24)) (.imp (ConstructionBaseWeights.digits (0 : Fin 24) (14 : Fin 24) (15 : Fin 24) (16 : Fin 24))
    (.imp (Project.Formula.isSuccessor (.bound (17 : Fin 24)) (.bound (16 : Fin 24))) (.imp (.mem (.bound
    (17 : Fin 24)) (.bound (0 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (13 :
    Fin 24) (18 : Fin 24) (19 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (9 : Fin
    24) (18 : Fin 24) (20 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (10 : Fin
    24) (18 : Fin 24) (21 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin
    24) (20 : Fin 24) (22 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin
    24) (21 : Fin 24) (23 : Fin 24))) (.existsE (.existsE (.existsE (.existsE (.conj (recipe (0 : Fin
    24).succ.succ.succ.succ (1 : Fin 24).succ.succ.succ.succ (17 : Fin 24).succ.succ.succ.succ (19 : Fin
    24).succ.succ.succ.succ (22 : Fin 24).succ.succ.succ.succ (23 : Fin 24).succ.succ.succ.succ (3 : Fin
    (24+4)) (2 : Fin (24+4)) (1 : Fin (24+4)) (0 : Fin (24+4))) (.conj (interval (0 : Fin
    24).succ.succ.succ.succ (1 : Fin 24).succ.succ.succ.succ (19 : Fin 24).succ.succ.succ.succ (22 : Fin
    24).succ.succ.succ.succ (23 : Fin 24).succ.succ.succ.succ (3 : Fin (24+4)) (2 : Fin (24+4)) (1 : Fin
    (24+4)) (0 : Fin (24+4))) (outsideBound (3 : Fin 24).succ.succ.succ.succ (4 : Fin
    24).succ.succ.succ.succ (7 : Fin 24).succ.succ.succ.succ (8 : Fin 24).succ.succ.succ.succ (12 : Fin
    24).succ.succ.succ.succ (18 : Fin 24).succ.succ.succ.succ (21 : Fin 24).succ.succ.succ.succ (0 : Fin
    (24+4))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs
    [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.exitGraph_freeClosed,ConstructionProbeLetterFloorSyntax.floorLaws_freeClosed,ConstructionProbeCostBoundsSyntax.costBounds_freeClosed,uniformMargins_freeClosed,ConstructionBaseWeights.digits_freeClosed,recipe_freeClosed,interval_freeClosed,outsideBound_freeClosed]

theorem letter_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence letterSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) letterSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only
  [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics
  hM,ConstructionRealCuts.cutCarrier_semantics hM,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality
  hM),ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq
  (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M :=
  M),ConstructionProbeAlphabet.exitGraph_semantics
  hM,ConstructionProbeLetterFloorSyntax.floorLaws_semantics
  hM,ConstructionProbeCostBoundsSyntax.costBounds_semantics hM,uniformMargins_semantics
  hM,ConstructionBaseWeights.digits_semantics,Project.Formula.satisfies_isSuccessor_iff,KuratowskiZF.source_edge,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,recipe_semantics
  hM,interval_semantics hM,outsideBound_semantics hM,Project.Term.eval_bound]
  exact exists_letter_interval hM

theorem letter_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence letterSentence) := ModelTransfer.derives (fun _ hM => letter_models hM)

end PPAC.Migration.ConstructionProbeIntervalsSyntax
