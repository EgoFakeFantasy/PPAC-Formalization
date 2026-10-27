/- Pinned Diagrams.OverlapPrescription.CopyRel/Valid and MergerWords.rel_mul.
The literal optional start table and pair identifications are internal graphs;
validity is required for the GIVEN relation, never its transitive closure.
Consumer: actual quotient Copies and its right free action in MergerWords. -/
import PPAC.Migration.ConstructionProbeLetters
import PPAC.Migration.ConstructionProbeGateCap

namespace PPAC.Migration.ConstructionMergerRelations
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Start (P i j a b : M.Carrier .set) : Prop :=
  ∃ ab, PureKuratowski.Code M ab a b ∧ Product P i j ab

def Prescription (n D P : M.Carrier .set) : Prop :=
  (∀ i j a b, Start P i j a b → (Project.FirstOrderSemantics.reduct M).mem i n ∧
    (Project.FirstOrderSemantics.reduct M).mem j n ∧ (Project.FirstOrderSemantics.reduct M).mem a D ∧
    (Project.FirstOrderSemantics.reduct M).mem b D) ∧
  (∀ i j a b c d, Start P i j a b → Start P i j c d → a = c ∧ b = d)

def CopyRel (n D mul P i x j y : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i n ∧ (Project.FirstOrderSemantics.reduct M).mem x D ∧
  (Project.FirstOrderSemantics.reduct M).mem j n ∧ (Project.FirstOrderSemantics.reduct M).mem y D ∧
  ((i = j ∧ x = y) ∨ (i ≠ j ∧ ∃ a b t, Start P i j a b ∧
    (Project.FirstOrderSemantics.reduct M).mem t D ∧ Product mul a t x ∧ Product mul b t y))

def Valid (n D mul P : M.Carrier .set) : Prop :=
  (∀ i x, (Project.FirstOrderSemantics.reduct M).mem i n → (Project.FirstOrderSemantics.reduct M).mem x D → CopyRel n D mul P i x i x) ∧
  (∀ i x j y, CopyRel n D mul P i x j y → CopyRel n D mul P j y i x) ∧
  (∀ i x j y k z, CopyRel n D mul P i x j y → CopyRel n D mul P j y k z → CopyRel n D mul P i x k z)

theorem rel_same_copy {n D mul P i x y : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i n) (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D) : CopyRel n D mul P i x i y ↔ x = y := by
  constructor
  · rintro ⟨_,_,_,_,h⟩
    rcases h with ⟨_,h⟩ | ⟨hne,_⟩
    · exact h
    · exact (hne rfl).elim
  · exact fun h => ⟨hi,hx,hi,hy,Or.inl ⟨rfl,h⟩⟩

theorem product_range {D mul e x y z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D) (hp : Product mul x y z) :
    (Project.FirstOrderSemantics.reduct M).mem z D := by
  obtain ⟨z',hz',hp'⟩ := (hm.2.1 x hx).1 y hy
  exact ((hm.2.1 x hx).2.1 y z' z hy hp' hp) ▸ hz'

theorem rel_mul {n D mul P e i x j y m xm ym : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m D)
    (h : CopyRel n D mul P i x j y) (hxm : Product mul x m xm) (hym : Product mul y m ym) :
    CopyRel n D mul P i xm j ym := by
  obtain ⟨hi,hx,hj,hy,h⟩ := h
  refine ⟨hi,product_range hm hx hmD hxm,hj,product_range hm hy hmD hym,?_⟩
  rcases h with ⟨rfl,rfl⟩ | ⟨hne,a,b,t,hStart,ht,hat,hbt⟩
  · exact Or.inl ⟨rfl,(hm.2.1 x hx).2.1 m xm ym hmD hxm hym⟩
  · obtain ⟨tm,htmD,htm⟩ := (hm.2.1 t ht).1 m hmD
    have hAB := hP.1 i j a b hStart
    exact Or.inr ⟨hne,a,b,tm,hStart,htmD,
      (hm.2.2 a t m x tm xm hAB.2.2.1 ht hmD hat htm).mp hxm,
      (hm.2.2 b t m y tm ym hAB.2.2.2 ht hmD hbt htm).mp hym⟩

def start {m : Nat} (P i j a b : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (PureKuratowskiProject.code (.bound 0) (.bound a.succ) (.bound b.succ))
  (ProjectSyntax.encode id (ForcingDiagramOrder.product P.succ i.succ j.succ 0))))

theorem start_freeClosed {m : Nat} (P i j a b : Fin m) : (start P i j a b).FreeClosed := by
  simp -implicitDefEqProofs [start,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem start_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P i j a b : Fin m) :
    Project.Formula.satisfies env (start P i j a b) ↔ Start (env.bound P) (env.bound i) (env.bound j) (env.bound a) (env.bound b) := by
  simp only [start,Start,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    Project.Term.eval_bound,
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def prescription {m : Nat} (n D P : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (start P.succ.succ.succ.succ 3 2 1 0) (.conj (.mem
  (.bound 3) (.bound n.succ.succ.succ.succ)) (.conj (.mem (.bound 2) (.bound n.succ.succ.succ.succ)) (.conj
  (.mem (.bound 1) (.bound D.succ.succ.succ.succ)) (.mem (.bound 0) (.bound D.succ.succ.succ.succ))))))))))
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (start P.succ.succ.succ.succ.succ.succ 5
  4 3 2) (.imp (start P.succ.succ.succ.succ.succ.succ 5 4 1 0) (.conj (Project.Formula.extensionalEq (.bound
  3) (.bound 1)) (Project.Formula.extensionalEq (.bound 2) (.bound 0))))))))))))

theorem prescription_freeClosed {m : Nat} (n D P : Fin m) : (prescription n D P).FreeClosed := by
  simp -implicitDefEqProofs [prescription,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,start_freeClosed]

theorem prescription_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D P : Fin m) :
    Project.Formula.satisfies env (prescription n D P) ↔ Prescription (env.bound n) (env.bound D) (env.bound P) := by
  simp only [prescription,Prescription,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),start_semantics hM]
  rfl

def rel {m : Nat} (n D mul P i x j y : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound i) (.bound n)) (.conj (.mem (.bound x) (.bound D)) (.conj (.mem (.bound j) (.bound
  n)) (.conj (.mem (.bound y) (.bound D)) (.disj (.conj (Project.Formula.extensionalEq (.bound i) (.bound
  j)) (Project.Formula.extensionalEq (.bound x) (.bound y))) (.conj (.neg (Project.Formula.extensionalEq
  (.bound i) (.bound j))) (.existsE (.existsE (.existsE (.conj (start P.succ.succ.succ i.succ.succ.succ
  j.succ.succ.succ 2 1) (.conj (.mem (.bound 0) (.bound D.succ.succ.succ)) (.conj (ProjectSyntax.encode id
  (ForcingDiagramOrder.product mul.succ.succ.succ 2 0 x.succ.succ.succ)) (ProjectSyntax.encode id
  (ForcingDiagramOrder.product mul.succ.succ.succ 1 0 y.succ.succ.succ))))))))))))))

theorem rel_freeClosed {m : Nat} (n D mul P i x j y : Fin m) : (rel n D mul P i x j y).FreeClosed := by
  simp -implicitDefEqProofs [rel,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,start_freeClosed]

theorem rel_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P i x j y : Fin m) :
    Project.Formula.satisfies env (rel n D mul P i x j y) ↔ CopyRel (env.bound n) (env.bound D) (env.bound mul) (env.bound P) (env.bound i) (env.bound x) (env.bound j) (env.bound y) := by
  simp only [rel,CopyRel,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),start_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def valid {m : Nat} (n D mul P : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound n.succ.succ)) (.imp (.mem (.bound 0) (.bound
  D.succ.succ)) (rel n.succ.succ D.succ.succ mul.succ.succ P.succ.succ 1 0 1 0))))) (.conj (.forallE
  (.forallE (.forallE (.forallE (.imp (rel n.succ.succ.succ.succ D.succ.succ.succ.succ
  mul.succ.succ.succ.succ P.succ.succ.succ.succ 3 2 1 0) (rel n.succ.succ.succ.succ D.succ.succ.succ.succ
  mul.succ.succ.succ.succ P.succ.succ.succ.succ 1 0 3 2)))))) (.forallE (.forallE (.forallE (.forallE
  (.forallE (.forallE (.imp (rel n.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ 5 4 3 2) (.imp (rel
  n.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ 3 2 1 0) (rel n.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ 5 4 1
  0)))))))))))

theorem valid_freeClosed {m : Nat} (n D mul P : Fin m) : (valid n D mul P).FreeClosed := by
  simp -implicitDefEqProofs [valid,Definitional.Formula.FreeClosed,rel_freeClosed]

theorem valid_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D mul P : Fin m) :
    Project.Formula.satisfies env (valid n D mul P) ↔ Valid (env.bound n) (env.bound D) (env.bound mul) (env.bound P) := by
  simp only [valid,Valid,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    rel_semantics hM]
  rfl

end PPAC.Migration.ConstructionMergerRelations
