import PPAC.Migration.Internal.ObjectProjectSourceCode

/-! Actual twelve-constructor Project compiler cases; recursive queries are explicit object relations. -/
namespace PPAC.Migration.Internal.ProjectCompilerCaseSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def relation {k m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (x b q : Fin m) : Formula m :=
  P.rename (Fin.lastCases q (Fin.lastCases b (Fin.lastCases x ρ)))

def queried {k m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (n x b q : Fin m) : Formula m :=
  (Formula.mem x n).conj (relation P ρ x b q)

def advanced {k m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (n x b q : Fin m) : Formula m := .ex
  ((successor (Fin.last m) b.castSucc).conj
    (queried P (fun i => (ρ i).castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc))

def check {k m} (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m) (n x b q : Fin m) : Formula m :=
  if advance then advanced P ρ n x b q else queried P ρ n x b q

def constant {m} (truth : Bool) (w n q : Fin m) : Formula m :=
  (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).conj (.equal q n)

def atomicBody {m} (kind : Fin 3) (w b z n q : Fin m) : Formula (m+2) :=
  ProjectAtomicSyntax.compiled kind (old 2 w) (old 2 b) (old 2 z) (slot 2 0) (slot 2 1) (old 2 n) (old 2 q)

def atomicCase {m} (kind : Fin 3) (w b z n q : Fin m) : Formula m := existsMany 2 (atomicBody kind w b z n q)

def singleMatrix {k m} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q x y : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.singleCode tag w x n).conj
    ((check advance P ρ n x b y).conj (SyntaxLogicalSyntax.singleCode tag w y q))

def singleBody {k m} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q : Fin m) : Formula (m+2) :=
  singleMatrix tag advance P (fun i => old 2 (ρ i)) (old 2 w) (old 2 b) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1)

def singleCase {k m} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b n q : Fin m) : Formula m :=
  existsMany 2 (singleBody tag advance P ρ w b n q)

def binaryMatrix {k m} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q x y X Y : Fin m) : Formula m :=
  (SyntaxLogicalSyntax.binaryCode kind w x y n).conj
    ((queried P ρ n x b X).conj ((queried P ρ n y b Y).conj (SyntaxLogicalSyntax.binaryCode kind w X Y q)))

def binaryBody {k m} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b n q : Fin m) : Formula (m+4) :=
  binaryMatrix kind P (fun i => old 4 (ρ i)) (old 4 w) (old 4 b) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def binaryCase {k m} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b n q : Fin m) : Formula m :=
  existsMany 4 (binaryBody kind P ρ w b n q)

def cases {k m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b z n q : Fin m) : Formula m :=
  (constant false w n q).disj ((constant true w n q).disj
    ((atomicCase 0 w b z n q).disj ((atomicCase 1 w b z n q).disj ((atomicCase 2 w b z n q).disj
      ((singleCase 4 false P ρ w b n q).disj ((binaryCase 0 P ρ w b n q).disj
        ((binaryCase 1 P ρ w b n q).disj ((binaryCase 2 P ρ w b n q).disj ((binaryCase 3 P ρ w b n q).disj
          ((singleCase 9 true P ρ w b n q).disj (singleCase 10 true P ρ w b n q)))))))))))

theorem relation_rename {k m l} (P : Formula (k+3)) (ρ : Fin k → Fin m) (x b q : Fin m) (σ : Fin m → Fin l) :
    (relation P ρ x b q).rename σ = relation P (fun i => σ (ρ i)) (σ x) (σ b) (σ q) := by
  simp only [relation, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
  · simp only [Fin.lastCases_castSucc]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.lastCases_last]
      · simp only [Fin.lastCases_castSucc]

theorem queried_rename {k m l} (P : Formula (k+3)) (ρ : Fin k → Fin m) (n x b q : Fin m) (σ : Fin m → Fin l) :
    (queried P ρ n x b q).rename σ = queried P (fun i => σ (ρ i)) (σ n) (σ x) (σ b) (σ q) := by
  simp only [queried, Formula.rename, relation_rename]

theorem advanced_rename {k m l} (P : Formula (k+3)) (ρ : Fin k → Fin m) (n x b q : Fin m) (σ : Fin m → Fin l) :
    (advanced P ρ n x b q).rename σ = advanced P (fun i => σ (ρ i)) (σ n) (σ x) (σ b) (σ q) := by
  simp only [advanced, Formula.rename, successor_rename, queried_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem check_rename {k m l} (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m) (n x b q : Fin m) (σ : Fin m → Fin l) :
    (check advance P ρ n x b q).rename σ = check advance P (fun i => σ (ρ i)) (σ n) (σ x) (σ b) (σ q) := by
  cases advance <;> simp only [check, Bool.false_eq_true, ↓reduceIte, advanced_rename, queried_rename]

theorem constant_rename {m l} (truth : Bool) (w n q : Fin m) (σ : Fin m → Fin l) :
    (constant truth w n q).rename σ = constant truth (σ w) (σ n) (σ q) := by
  simp only [constant, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]

theorem atomicBody_lift {m l} (kind : Fin 3) (w b z n q : Fin m) (σ : Fin m → Fin l) :
    (atomicBody kind w b z n q).rename (lift 2 σ) = atomicBody kind (σ w) (σ b) (σ z) (σ n) (σ q) := by
  simp only [atomicBody, ProjectAtomicSyntax.compiled_rename, lift_old, lift_slot]

theorem atomicCase_rename {m l} (kind : Fin 3) (w b z n q : Fin m) (σ : Fin m → Fin l) :
    (atomicCase kind w b z n q).rename σ = atomicCase kind (σ w) (σ b) (σ z) (σ n) (σ q) := by
  simp only [atomicCase, existsMany_rename, atomicBody_lift]

theorem singleMatrix_rename {k m l} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q x y : Fin m) (σ : Fin m → Fin l) :
    (singleMatrix tag advance P ρ w b n q x y).rename σ =
      singleMatrix tag advance P (fun i => σ (ρ i)) (σ w) (σ b) (σ n) (σ q) (σ x) (σ y) := by
  simp only [singleMatrix, Formula.rename, SyntaxLogicalSyntax.singleCode_rename, check_rename]

theorem singleBody_lift {k m l} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q : Fin m) (σ : Fin m → Fin l) :
    (singleBody tag advance P ρ w b n q).rename (lift 2 σ) = singleBody tag advance P (fun i => σ (ρ i)) (σ w) (σ b) (σ n) (σ q) := by
  simp only [singleBody, singleMatrix_rename, lift_old, lift_slot]

theorem singleCase_rename {k m l} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q : Fin m) (σ : Fin m → Fin l) :
    (singleCase tag advance P ρ w b n q).rename σ = singleCase tag advance P (fun i => σ (ρ i)) (σ w) (σ b) (σ n) (σ q) := by
  simp only [singleCase, existsMany_rename, singleBody_lift]

theorem binaryMatrix_rename {k m l} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q x y X Y : Fin m) (σ : Fin m → Fin l) :
    (binaryMatrix kind P ρ w b n q x y X Y).rename σ =
      binaryMatrix kind P (fun i => σ (ρ i)) (σ w) (σ b) (σ n) (σ q) (σ x) (σ y) (σ X) (σ Y) := by
  simp only [binaryMatrix, Formula.rename, SyntaxLogicalSyntax.binaryCode_rename, queried_rename]

theorem binaryBody_lift {k m l} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q : Fin m) (σ : Fin m → Fin l) :
    (binaryBody kind P ρ w b n q).rename (lift 4 σ) = binaryBody kind P (fun i => σ (ρ i)) (σ w) (σ b) (σ n) (σ q) := by
  simp only [binaryBody, binaryMatrix_rename, lift_old, lift_slot]

theorem binaryCase_rename {k m l} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q : Fin m) (σ : Fin m → Fin l) :
    (binaryCase kind P ρ w b n q).rename σ = binaryCase kind P (fun i => σ (ρ i)) (σ w) (σ b) (σ n) (σ q) := by
  simp only [binaryCase, existsMany_rename, binaryBody_lift]

theorem cases_rename {k m l} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b z n q : Fin m) (σ : Fin m → Fin l) :
    (cases P ρ w b z n q).rename σ = cases P (fun i => σ (ρ i)) (σ w) (σ b) (σ z) (σ n) (σ q) := by
  simp only [cases, Formula.rename, constant_rename, atomicCase_rename, singleCase_rename, binaryCase_rename]

end PPAC.Migration.Internal.ProjectCompilerCaseSyntax
