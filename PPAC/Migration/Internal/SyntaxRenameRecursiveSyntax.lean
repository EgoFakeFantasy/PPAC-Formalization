import PPAC.Migration.Internal.SyntaxRenameJudgment

/-! 不带历史参数的完整重命名递归AST；子判断、严格源码界及实际bound码提升。 -/
namespace PPAC.Migration.Internal.SyntaxRenameRecursiveSyntax
open Source SourceAlgebra SourceLogic SyntaxLogicalSyntax SyntaxRenameJudgmentSyntax
open SyntaxMapCodeSyntax

def advancedBody {m} (w x r s a b c d q : Fin m) : Formula (m+3) :=
  (SyntaxMapLiftSyntax.codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
  (renamed w.castSucc.castSucc.castSucc (Fin.last (m+2)) s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
    b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc)

def advanced {m} (w x r s a b c d q : Fin m) : Formula m := .ex (.ex (.ex (advancedBody w x r s a b c d q)))

theorem advanced_rename {m k} (w x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (advanced w x r s a b c d q).rename ρ = advanced (ρ w) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  simp only [advanced, advancedBody, Formula.rename, SyntaxMapLiftSyntax.codedLift_rename, renamed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def check {m} (advance : Bool) (w x r s a b c d q : Fin m) : Formula m :=
  if advance then advanced w x r s a b c d q else renamed w r s a b c d x q

theorem check_rename {m k} (advance : Bool) (w x r s a b c d q : Fin m) (ρ : Fin m → Fin k) :
    (check advance w x r s a b c d q).rename ρ = check advance (ρ w) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ q) := by
  cases advance <;> simp only [check, Bool.false_eq_true, ↓reduceIte, renamed_rename, advanced_rename]

def singleData {m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) : Formula m :=
  (singleCode tag w x n).conj ((Formula.mem x n).conj ((singleCode tag w X q).conj (check advance w x r s a b c d X)))

def singleBody {m} (tag : Nat) (advance : Bool) (w r s a b c d n q : Fin m) : Formula (m+2) :=
  singleData tag advance w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def single {m} (tag : Nat) (advance : Bool) (w r s a b c d n q : Fin m) : Formula m := .ex (.ex (singleBody tag advance w r s a b c d n q))

theorem singleData_rename {m k} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) (ρ : Fin m → Fin k) :
    (singleData tag advance w r s a b c d n q x X).rename ρ = singleData tag advance (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ x) (ρ X) := by
  simp only [singleData, Formula.rename, singleCode_rename, check_rename]

theorem single_rename {m k} (tag : Nat) (advance : Bool) (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (single tag advance w r s a b c d n q).rename ρ = single tag advance (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [single, singleBody, Formula.rename, singleData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_single {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m)
    (hd : Derives Γ (singleData tag advance w r s a b c d n q x X)) : Derives Γ (single tag advance w r s a b c d n q) := by
  apply Derives.exI x
  apply Derives.exI X
  simpa only [singleBody, Formula.instantiate, Formula.rename, singleData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

def binaryData {m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) : Formula m :=
  (binaryCode kind w x y n).conj ((Formula.mem x n).conj ((Formula.mem y n).conj ((binaryCode kind w X Y q).conj ((renamed w r s a b c d x X).conj (renamed w r s a b c d y Y)))))

def binaryBody {m} (kind : Fin 4) (w r s a b c d n q : Fin m) : Formula (m+4) :=
  binaryData kind w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def binary {m} (kind : Fin 4) (w r s a b c d n q : Fin m) : Formula m := .ex (.ex (.ex (.ex (binaryBody kind w r s a b c d n q))))

theorem binaryData_rename {m k} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (binaryData kind w r s a b c d n q x y X Y).rename ρ = binaryData kind (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [binaryData, Formula.rename, binaryCode_rename, renamed_rename]

theorem binary_rename {m k} (kind : Fin 4) (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (binary kind w r s a b c d n q).rename ρ = binary kind (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [binary, binaryBody, Formula.rename, binaryData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_binary {m} {Γ : Context m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m)
    (hd : Derives Γ (binaryData kind w r s a b c d n q x y X Y)) : Derives Γ (binary kind w r s a b c d n q) := by
  apply Derives.exI x
  apply Derives.exI y
  apply Derives.exI X
  apply Derives.exI Y
  simpa only [binaryBody, Formula.instantiate, Formula.rename, binaryData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

def cases {m} (w R S r s a b c d n q : Fin m) : Formula m :=
  ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).disj (SyntaxRenameAtomSyntax.nullary true w a b c d n q)).disj
    ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).disj
      ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).disj
        ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).disj
          ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).disj
            ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).disj
              ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).disj
                ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).disj
                  ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).disj
                    (SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q)))))))))

theorem cases_rename {m k} (w R S r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (cases w R S r s a b c d n q).rename ρ = cases (ρ w) (ρ R) (ρ S) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [cases, Formula.rename, SyntaxRenameAtomSyntax.nullary_rename, SyntaxRenameAtomSyntax.membership_rename, SyntaxRenameAtomSyntax.equality_rename, SyntaxRenameRecursiveSyntax.single_rename, SyntaxRenameRecursiveSyntax.binary_rename]

def localRenameData {m} (w R S a b c d n q r s : Fin m) : Formula m :=
  (encoded w r a c R).conj ((encoded w s b d S).conj (cases w R S r s a b c d n q))

def localRenameBody {m} (w R S a b c d n q : Fin m) : Formula (m+2) :=
  localRenameData w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def localRename {m} (w R S a b c d n q : Fin m) : Formula m := .ex (.ex (localRenameBody w R S a b c d n q))

theorem localRenameData_rename {m k} (w R S a b c d n q r s : Fin m) (ρ : Fin m → Fin k) :
    (localRenameData w R S a b c d n q r s).rename ρ = localRenameData (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) (ρ r) (ρ s) := by
  simp only [localRenameData, Formula.rename, encoded_rename, cases_rename]

theorem localRename_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (localRename w R S a b c d n q).rename ρ = localRename (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [localRename, localRenameBody, Formula.rename, localRenameData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_localRename {m} {Γ : Context m} (w R S a b c d n q r s : Fin m)
    (hd : Derives Γ (localRenameData w R S a b c d n q r s)) : Derives Γ (localRename w R S a b c d n q) := by
  apply Derives.exI r
  apply Derives.exI s
  simpa only [localRenameBody, Formula.instantiate, Formula.rename, localRenameData_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

def content {m} (w R S a b c d n q : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n a b).conj (localRename w R S a b c d n q)

theorem content_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (content w R S a b c d n q).rename ρ = content (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [content, Formula.rename, FormulaCodeSyntax.formulaCode_rename, localRename_rename]

def criterion {m} (w r s a b c d n q : Fin m) : Formula m :=
  (Formula.mem n w).conj ((SyntaxRenameStateSyntax.legal w r s a b c d q).conj (content w r s a b c d n q))

theorem criterion_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (criterion w r s a b c d n q).rename ρ = criterion (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [criterion, Formula.rename, SyntaxRenameStateSyntax.legal_rename, content_rename]
end PPAC.Migration.Internal.SyntaxRenameRecursiveSyntax
