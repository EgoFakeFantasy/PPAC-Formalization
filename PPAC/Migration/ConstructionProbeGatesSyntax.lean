/- Pure membership formulas for the literal ProbeGates relations and source suffix gate theorem. -/
import PPAC.Migration.ConstructionProbeGates

namespace PPAC.Migration.ConstructionProbeGatesSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeGates
open ConstructionProbeRaw (raw raw_freeClosed raw_semantics old old_freeClosed old_semantics cons cons_freeClosed cons_semantics)
open ConstructionProbeRawActionSyntax (headDiv headDiv_freeClosed headDiv_semantics)
open ConstructionProbeLetterAction (letterAct letterAct_freeClosed letterAct_semantics)
open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics inCone inCone_freeClosed inCone_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def headNone {m : Nat} (zero D q : Fin m) : Project.Formula 1 m :=
  .existsE (old zero.succ D.succ 0 q.succ)

def headSome {m : Nat} (w D S q s : Fin m) : Project.Formula 1 m :=
  .existsE (cons w.succ D.succ S.succ s.succ 0 q.succ)

def gate {m : Nat} (w D S zero mul A W G q s g : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound W.succ)) (.iff (.conj (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ G.succ q.succ 0)) (.neg (headSome w.succ D.succ S.succ 0 s.succ)))
  (headDiv w.succ D.succ S.succ zero.succ mul.succ A.succ g.succ 0))))

def headLaws {m : Nat} (w D S zero mul A b W E : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (raw w.succ D.succ S.succ 0) (.iff (headNone zero.succ D.succ 0) (.neg (.existsE
  (headSome w.succ.succ D.succ.succ S.succ.succ 1 0)))))) (.conj (.forallE (.forallE (.forallE (.imp
  (headSome w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 2 1) (.imp (headSome w.succ.succ.succ
  D.succ.succ.succ S.succ.succ.succ 2 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))) (.conj (.forallE (.forallE (.imp
  (.mem (.bound 1) (.bound W.succ.succ)) (.iff (headSome w.succ.succ D.succ.succ S.succ.succ 1 0) (.existsE
  (.conj (.mem (.bound 0) (.bound W.succ.succ.succ)) (.conj (.neg (headDiv w.succ.succ.succ D.succ.succ.succ
  S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ 0)) (cons
  w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 1 0 2)))))))) (.conj (.forallE (.forallE
  (.forallE (.imp (headSome w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 1 0) (.iff (headDiv
  w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ 2
  1) (inCone S.succ.succ.succ A.succ.succ.succ 2 0)))))) (.forallE (.forallE (.forallE (.imp (letterAct
  w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ
  b.succ.succ.succ W.succ.succ.succ E.succ.succ.succ 2 1 0) (.iff (.neg (headSome w.succ.succ.succ
  D.succ.succ.succ S.succ.succ.succ 0 2)) (headDiv w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ
  zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ 1))))))))))

def gateLaws {m : Nat} (w D S zero mul A W G : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (gate w.succ.succ.succ.succ D.succ.succ.succ.succ
  S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ
  W.succ.succ.succ.succ G.succ.succ.succ.succ 3 2 1) (.imp (.mem (.bound 0) (.bound W.succ.succ.succ.succ))
  (.imp (headDiv w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ zero.succ.succ.succ.succ
  mul.succ.succ.succ.succ A.succ.succ.succ.succ 1 0) (.neg (headSome w.succ.succ.succ.succ
  D.succ.succ.succ.succ S.succ.succ.succ.succ 0 2))))))))) (.conj (.forallE (.forallE (.forallE (.forallE
  (.forallE (.imp (gate w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ 4 3 2) (.imp (old zero.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ 1 0) (.imp (.mem (.bound 0) (.bound W.succ.succ.succ.succ.succ)) (.iff
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ 4 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ 2 1))))))))))) (.forallE (.forallE (.forallE
  (.forallE (.forallE (.imp (gate w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ 4 3 2) (.imp (headSome
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ 4 3) (.imp (.neg (headDiv
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 1 4)) (.imp (.mem
  (.bound 0) (.bound W.succ.succ.succ.succ.succ)) (.iff (.conj (headDiv w.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 1 0) (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ 4 0))) (.conj (headDiv
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 1 0) (headDiv
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 2 0))))))))))))))

theorem headNone_freeClosed {m : Nat} (zero D q : Fin m) : (headNone zero D q).FreeClosed := by
  simp -implicitDefEqProofs [headNone,Definitional.Formula.FreeClosed,old_freeClosed]

theorem headNone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D q : Fin m) :
    Project.Formula.satisfies env (headNone zero D q) ↔
      HeadNone (env.bound zero) (env.bound D) (env.bound q) := by
  simp only [headNone,HeadNone,Project.Formula.satisfies_exists_iff,old_semantics hM]
  rfl

theorem headSome_freeClosed {m : Nat} (w D S q s : Fin m) : (headSome w D S q s).FreeClosed := by
  simp -implicitDefEqProofs [headSome,Definitional.Formula.FreeClosed,cons_freeClosed]

theorem headSome_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S q s : Fin m) :
    Project.Formula.satisfies env (headSome w D S q s) ↔
      HeadSome (env.bound w) (env.bound D) (env.bound S) (env.bound q) (env.bound s) := by
  simp only [headSome,HeadSome,Project.Formula.satisfies_exists_iff,cons_semantics hM]
  rfl

theorem gate_freeClosed {m : Nat} (w D S zero mul A W G q s g : Fin m) : (gate w D S zero mul A W G q s g).FreeClosed := by
  simp -implicitDefEqProofs [gate,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,headSome_freeClosed,headDiv_freeClosed]

theorem gate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W G q s g : Fin m) :
    Project.Formula.satisfies env (gate w D S zero mul A W G q s g) ↔
      Gate (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound W) (env.bound G) (env.bound q) (env.bound s) (env.bound g) := by
  simp only [gate,Gate,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M),headSome_semantics hM,headDiv_semantics hM]
  rfl

theorem headLaws_freeClosed {m : Nat} (w D S zero mul A b W E : Fin m) : (headLaws w D S zero mul A b W E).FreeClosed := by
  simp -implicitDefEqProofs [headLaws,Definitional.Formula.FreeClosed,raw_freeClosed,headNone_freeClosed,headSome_freeClosed,cons_freeClosed,headDiv_freeClosed,inCone_freeClosed,letterAct_freeClosed,Project.Formula.extensionalEq_freeClosed_iff]

theorem headLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E : Fin m) :
    Project.Formula.satisfies env (headLaws w D S zero mul A b W E) ↔
      HeadLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) := by
  simp only [headLaws,HeadLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,Project.Term.eval_bound,raw_semantics hM,headNone_semantics hM,headSome_semantics hM,cons_semantics hM,headDiv_semantics hM,inCone_semantics hM,letterAct_semantics hM]
  rfl

theorem gateLaws_freeClosed {m : Nat} (w D S zero mul A W G : Fin m) : (gateLaws w D S zero mul A W G).FreeClosed := by
  simp -implicitDefEqProofs [gateLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,gate_freeClosed,headSome_freeClosed,headDiv_freeClosed,old_freeClosed]

theorem gateLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W G : Fin m) :
    Project.Formula.satisfies env (gateLaws w D S zero mul A W G) ↔
      GateLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound W) (env.bound G) := by
  simp only [gateLaws,GateLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M),gate_semantics hM,headSome_semantics hM,headDiv_semantics hM,old_semantics hM]
  rfl

def lawsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 12
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 12))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    12))) (.imp (.mem (.bound (3 : Fin 12)) (.bound (0 : Fin 12))) (.imp (alphabet (1 : Fin 12) (4 : Fin 12)
    (9 : Fin 12) (2 : Fin 12) (10 : Fin 12) (5 : Fin 12) (8 : Fin 12)) (.imp (wordCarrier (0 : Fin 12) (1 :
    Fin 12) (2 : Fin 12) (4 : Fin 12) (5 : Fin 12) (6 : Fin 12) (7 : Fin 12)) (.conj (headLaws (0 : Fin 12) (1
    : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 : Fin 12) (5 : Fin 12) (6 : Fin 12) (7 : Fin 12) (8 : Fin 12))
    (gateLaws (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 : Fin 12) (5 : Fin 12) (7 : Fin 12) (11 :
    Fin 12))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,wordCarrier_freeClosed,headLaws_freeClosed,gateLaws_freeClosed]

theorem laws_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence lawsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) lawsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_conj_iff,alphabet_semantics hM,wordCarrier_semantics hM,
    headLaws_semantics hM,gateLaws_semantics hM]
  exact fun hw hz hzw hAlpha hW => ⟨head_laws hM hw hz hzw hAlpha hW,gate_laws hM hw hz⟩

theorem laws_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence lawsSentence) := ModelTransfer.derives (fun _ hM => laws_models hM)

def suffixGateSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 20
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 20))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    20))) (.imp (.mem (.bound (3 : Fin 20)) (.bound (0 : Fin 20))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 20) (4 : Fin 20) (9 : Fin 20))) (.imp (alphabet (1 : Fin
    20) (4 : Fin 20) (9 : Fin 20) (2 : Fin 20) (10 : Fin 20) (5 : Fin 20) (8 : Fin 20)) (.imp (wordCarrier (0
    : Fin 20) (1 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20) (6 : Fin 20) (7 : Fin 20)) (.imp (.mem
    (.bound (6 : Fin 20)) (.bound (1 : Fin 20))) (.imp (multiplicationGraph (0 : Fin 20) (1 : Fin 20) (2 : Fin
    20) (3 : Fin 20) (4 : Fin 20) (5 : Fin 20) (6 : Fin 20) (7 : Fin 20) (8 : Fin 20) (11 : Fin 20)) (.imp
    (old (3 : Fin 20) (1 : Fin 20) (9 : Fin 20) (12 : Fin 20)) (.imp (cons (0 : Fin 20) (1 : Fin 20) (2 : Fin
    20) (13 : Fin 20) (14 : Fin 20) (15 : Fin 20)) (.imp (.mem (.bound (14 : Fin 20)) (.bound (7 : Fin 20)))
    (.imp (.neg (headDiv (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (5 : Fin 20) (6 :
    Fin 20) (14 : Fin 20))) (.imp (.mem (.bound (16 : Fin 20)) (.bound (1 : Fin 20))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (4 : Fin 20) (6 : Fin 20) (16 : Fin 20) (17 : Fin
    20))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (8 : Fin 20) (13 : Fin 20) (18 : Fin 20)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product (4 : Fin 20) (18 : Fin 20) (16 : Fin 20) (19 :
    Fin 20))) (.imp (.forallE (.imp (.mem (.bound 0) (.bound (7 : Fin 20).succ)) (.iff (.conj
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (7 : Fin 20).succ (11 : Fin 20).succ (14 : Fin
    20).succ 0)) (headDiv (0 : Fin 20).succ (1 : Fin 20).succ (2 : Fin 20).succ (3 : Fin 20).succ (4 : Fin
    20).succ (5 : Fin 20).succ (6 : Fin 20).succ 0)) (headDiv (0 : Fin 20).succ (1 : Fin 20).succ (2 : Fin
    20).succ (3 : Fin 20).succ (4 : Fin 20).succ (5 : Fin 20).succ (17 : Fin 20).succ 0)))) (gate (0 : Fin 20)
    (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (5 : Fin 20) (7 : Fin 20) (11 : Fin 20) (15 : Fin 20)
    (13 : Fin 20) (19 : Fin 20)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,wordCarrier_freeClosed,gate_freeClosed,
      old_freeClosed,cons_freeClosed,headDiv_freeClosed,multiplicationGraph_freeClosed]

theorem suffixGate_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence suffixGateSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) suffixGateSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),alphabet_semantics hM,wordCarrier_semantics hM,
    multiplicationGraph_semantics hM,old_semantics hM,cons_semantics hM,headDiv_semantics hM,
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M),
    gate_semantics hM]
  exact fun hw hz hzw hm hAlpha hW hb hG hUnit hCons hY hnot hu hbu hex hgu hInt =>
    gate_of_suffix_intersection hM hw hz hzw hm hAlpha hW hb hG hUnit hCons hY hnot hu hbu hex hgu hInt

theorem suffixGate_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence suffixGateSentence) := ModelTransfer.derives (fun _ hM => suffixGate_models hM)

end PPAC.Migration.ConstructionProbeGatesSyntax
