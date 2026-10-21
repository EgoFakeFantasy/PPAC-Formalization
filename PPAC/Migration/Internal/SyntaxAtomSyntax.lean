import PPAC.Migration.Internal.ObjectSyntaxTerms

/-! 原公式的零元常量、membership编号0和原子/equal类型；保留精确原字段顺序及内部上下文。 -/
namespace PPAC.Migration.Internal.SyntaxAtomSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax

def two {m} (x y : Fin m) : Fin 2 → Fin m := Fin.cases x (Fin.cases y Fin.elim0)
def three {m} (s x y : Fin m) : Fin 3 → Fin m := Fin.cases s (two x y)

def zeroScalar {m} (w n : Fin m) : Formula m := constructor 0 0 w Fin.elim0 n

def nullaryTag (truth : Bool) : Nat := if truth then 1 else 0

def nullary {m} (truth : Bool) (w b f n : Fin m) : Formula m := (contexts w b f).conj
  (constructor 0 (nullaryTag truth) w Fin.elim0 n)

def memberCode {m} (w s x y n : Fin m) : Formula m := constructor 3 2 w (three s x y) n

def equalCode {m} (w x y n : Fin m) : Formula m := constructor 2 3 w (two x y) n

def memberTypes {m} (w b f s x y : Fin m) : Formula m := (zeroScalar w s).conj ((term w b f x).conj (term w b f y))
def equalTypes {m} (w b f x y : Fin m) : Formula m := (term w b f x).conj (term w b f y)

def memberAt {m} (w b f s x y n : Fin m) : Formula m := (memberTypes w b f s x y).conj (memberCode w s x y n)
def equalAt {m} (w b f x y n : Fin m) : Formula m := (equalTypes w b f x y).conj (equalCode w x y n)

def memberBody {m} (w b f n : Fin m) : Formula (m+3) := memberAt w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
  f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc

def equalBody {m} (w b f n : Fin m) : Formula (m+2) := equalAt w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc
  (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc

def membership {m} (w b f n : Fin m) : Formula m := (contexts w b f).conj (.ex (.ex (.ex (memberBody w b f n))))
def equality {m} (w b f n : Fin m) : Formula m := (contexts w b f).conj (.ex (.ex (equalBody w b f n)))

def atomic {m} (w b f n : Fin m) : Formula m := ((nullary false w b f n).disj (nullary true w b f n)).disj
  ((membership w b f n).disj (equality w b f n))

def existsMembership {m} (w b f x y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (.ex
    (memberAt w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc)))

def existsEquality {m} (w b f x y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (equalAt w.castSucc b.castSucc f.castSucc x.castSucc y.castSucc (Fin.last m)))

def existsNullary {m} (truth : Bool) (w b f : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (nullary truth w.castSucc b.castSucc f.castSucc (Fin.last m)))

theorem zero_map {m k} (r : Fin m → Fin k) : (fun i : Fin 0 => r (Fin.elim0 i)) = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

theorem two_map {m k} (x y : Fin m) (r : Fin m → Fin k) : (fun i => r (two x y i)) = two (r x) (r y) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun q => Fin.elim0 q) j

theorem three_map {m k} (s x y : Fin m) (r : Fin m → Fin k) : (fun i => r (three s x y i)) = three (r s) (r x) (r y) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact congrFun (two_map x y r) j

theorem zeroScalar_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (zeroScalar w n).rename r = zeroScalar (r w) (r n) := by
  simp only [zeroScalar, constructor_rename, zero_map]

theorem nullary_rename {m k} (truth : Bool) (w b f n : Fin m) (r : Fin m → Fin k) : (nullary truth w b f n).rename r = nullary truth (r w) (r b) (r f) (r n) := by
  simp only [nullary, Formula.rename, contexts_rename, constructor_rename, zero_map]

theorem memberCode_rename {m k} (w s x y n : Fin m) (r : Fin m → Fin k) : (memberCode w s x y n).rename r = memberCode (r w) (r s) (r x) (r y) (r n) := by
  simp only [memberCode, constructor_rename, three_map]

theorem equalCode_rename {m k} (w x y n : Fin m) (r : Fin m → Fin k) : (equalCode w x y n).rename r = equalCode (r w) (r x) (r y) (r n) := by
  simp only [equalCode, constructor_rename, two_map]

theorem memberTypes_rename {m k} (w b f s x y : Fin m) (r : Fin m → Fin k) : (memberTypes w b f s x y).rename r = memberTypes (r w) (r b) (r f) (r s) (r x) (r y) := by
  simp only [memberTypes, Formula.rename, zeroScalar_rename, term_rename]

theorem equalTypes_rename {m k} (w b f x y : Fin m) (r : Fin m → Fin k) : (equalTypes w b f x y).rename r = equalTypes (r w) (r b) (r f) (r x) (r y) := by
  simp only [equalTypes, Formula.rename, term_rename]

theorem memberAt_rename {m k} (w b f s x y n : Fin m) (r : Fin m → Fin k) : (memberAt w b f s x y n).rename r = memberAt (r w) (r b) (r f) (r s) (r x) (r y) (r n) := by
  simp only [memberAt, Formula.rename, memberTypes_rename, memberCode_rename]

theorem equalAt_rename {m k} (w b f x y n : Fin m) (r : Fin m → Fin k) : (equalAt w b f x y n).rename r = equalAt (r w) (r b) (r f) (r x) (r y) (r n) := by
  simp only [equalAt, Formula.rename, equalTypes_rename, equalCode_rename]

theorem membership_rename {m k} (w b f n : Fin m) (r : Fin m → Fin k) : (membership w b f n).rename r = membership (r w) (r b) (r f) (r n) := by
  simp only [membership, memberBody, Formula.rename, contexts_rename, memberAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equality_rename {m k} (w b f n : Fin m) (r : Fin m → Fin k) : (equality w b f n).rename r = equality (r w) (r b) (r f) (r n) := by
  simp only [equality, equalBody, Formula.rename, contexts_rename, equalAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem atomic_rename {m k} (w b f n : Fin m) (r : Fin m → Fin k) : (atomic w b f n).rename r = atomic (r w) (r b) (r f) (r n) := by
  simp only [atomic, Formula.rename, nullary_rename, membership_rename, equality_rename]

theorem existsMembership_rename {m k} (w b f x y : Fin m) (r : Fin m → Fin k) : (existsMembership w b f x y).rename r = existsMembership (r w) (r b) (r f) (r x) (r y) := by
  simp only [existsMembership, Formula.rename, memberAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsEquality_rename {m k} (w b f x y : Fin m) (r : Fin m → Fin k) : (existsEquality w b f x y).rename r = existsEquality (r w) (r b) (r f) (r x) (r y) := by
  simp only [existsEquality, Formula.rename, equalAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsNullary_rename {m k} (truth : Bool) (w b f : Fin m) (r : Fin m → Fin k) :
    (existsNullary truth w b f).rename r = existsNullary truth (r w) (r b) (r f) := by
  simp only [existsNullary, Formula.rename, nullary_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.Internal.SyntaxAtomSyntax
