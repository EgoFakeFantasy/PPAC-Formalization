import PPAC.Migration.Internal.SyntaxContextRead

/-! 七种逻辑/量词局部分支的纯AST；真实历史状态读取及严格子码界。 -/
namespace PPAC.Migration.Internal.SyntaxLogicalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxContextReadSyntax

def singleCode {m} (tag : Nat) (w x n : Fin m) : Formula m := constructor 1 tag w (fun _ => x) n
def binaryTag (kind : Fin 4) : Nat := 5 + kind.val
def quantifierTag (universal : Bool) : Nat := if universal then 9 else 10
def binaryCode {m} (kind : Fin 4) (w x y n : Fin m) : Formula m := constructor 2 (binaryTag kind) w (two x y) n

def singleTypes {m} (advance : Bool) (w b f h x : Fin m) : Formula m :=
  (contexts w b f).conj (check advance h x b f)
def binaryTypes {m} (w b f h x y : Fin m) : Formula m :=
  (contexts w b f).conj ((read h x b f).conj (read h y b f))

def singleData {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : Formula m :=
  (singleCode tag w x n).conj ((Formula.mem x n).conj (check advance h x b f))
def binaryData {m} (kind : Fin 4) (w b f h x y n : Fin m) : Formula m :=
  (binaryCode kind w x y n).conj ((Formula.mem x n).conj ((Formula.mem y n).conj ((read h x b f).conj (read h y b f))))

def singleBody {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Formula (m+1) :=
  singleData tag advance w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m) n.castSucc
def binaryBody {m} (kind : Fin 4) (w b f h n : Fin m) : Formula (m+2) :=
  binaryData kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc

def single {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : Formula m :=
  (contexts w b f).conj (.ex (singleBody tag advance w b f h n))
def binary {m} (kind : Fin 4) (w b f h n : Fin m) : Formula m :=
  (contexts w b f).conj (.ex (.ex (binaryBody kind w b f h n)))

def negation {m} (w b f h n : Fin m) : Formula m := single 4 false w b f h n
def quantified {m} (universal : Bool) (w b f h n : Fin m) : Formula m :=
  single (quantifierTag universal) true w b f h n

def existsSingle {m} (tag : Nat) (advance : Bool) (w b f h x : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    ((single tag advance w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m)).conj
      (singleCode tag w.castSucc x.castSucc (Fin.last m))))
def existsBinary {m} (kind : Fin 4) (w b f h x y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    ((binary kind w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m)).conj
      (binaryCode kind w.castSucc x.castSucc y.castSucc (Fin.last m))))

theorem singleCode_rename {m k} (tag : Nat) (w x n : Fin m) (r : Fin m → Fin k) :
    (singleCode tag w x n).rename r = singleCode tag (r w) (r x) (r n) := by
  simp only [singleCode, constructor_rename]

theorem binaryCode_rename {m k} (kind : Fin 4) (w x y n : Fin m) (r : Fin m → Fin k) :
    (binaryCode kind w x y n).rename r = binaryCode kind (r w) (r x) (r y) (r n) := by
  simp only [binaryCode, constructor_rename, two_map]

theorem singleTypes_rename {m k} (advance : Bool) (w b f h x : Fin m) (r : Fin m → Fin k) :
    (singleTypes advance w b f h x).rename r = singleTypes advance (r w) (r b) (r f) (r h) (r x) := by
  simp only [singleTypes, Formula.rename, contexts_rename, check_rename]

theorem binaryTypes_rename {m k} (w b f h x y : Fin m) (r : Fin m → Fin k) :
    (binaryTypes w b f h x y).rename r = binaryTypes (r w) (r b) (r f) (r h) (r x) (r y) := by
  simp only [binaryTypes, Formula.rename, contexts_rename, read_rename]

theorem singleData_rename {m k} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) (r : Fin m → Fin k) :
    (singleData tag advance w b f h x n).rename r = singleData tag advance (r w) (r b) (r f) (r h) (r x) (r n) := by
  simp only [singleData, Formula.rename, singleCode_rename, check_rename]

theorem binaryData_rename {m k} (kind : Fin 4) (w b f h x y n : Fin m) (r : Fin m → Fin k) :
    (binaryData kind w b f h x y n).rename r = binaryData kind (r w) (r b) (r f) (r h) (r x) (r y) (r n) := by
  simp only [binaryData, Formula.rename, binaryCode_rename, read_rename]

theorem single_rename {m k} (tag : Nat) (advance : Bool) (w b f h n : Fin m) (r : Fin m → Fin k) :
    (single tag advance w b f h n).rename r = single tag advance (r w) (r b) (r f) (r h) (r n) := by
  simp only [single, singleBody, Formula.rename, contexts_rename, singleData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem binary_rename {m k} (kind : Fin 4) (w b f h n : Fin m) (r : Fin m → Fin k) :
    (binary kind w b f h n).rename r = binary kind (r w) (r b) (r f) (r h) (r n) := by
  simp only [binary, binaryBody, Formula.rename, contexts_rename, binaryData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsSingle_rename {m k} (tag : Nat) (advance : Bool) (w b f h x : Fin m) (r : Fin m → Fin k) :
    (existsSingle tag advance w b f h x).rename r = existsSingle tag advance (r w) (r b) (r f) (r h) (r x) := by
  simp only [existsSingle, Formula.rename, single_rename, singleCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsBinary_rename {m k} (kind : Fin 4) (w b f h x y : Fin m) (r : Fin m → Fin k) :
    (existsBinary kind w b f h x y).rename r = existsBinary kind (r w) (r b) (r f) (r h) (r x) (r y) := by
  simp only [existsBinary, Formula.rename, binary_rename, binaryCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_single {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m)
    (hc : Derives Γ (contexts w b f)) (hd : Derives Γ (singleData tag advance w b f h x n)) :
    Derives Γ (single tag advance w b f h n) := by
  apply Derives.conjI hc
  apply Derives.exI x
  simpa only [singleBody, Formula.instantiate, singleData_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem intro_binary {m} {Γ : Context m} (kind : Fin 4) (w b f h x y n : Fin m)
    (hc : Derives Γ (contexts w b f)) (hd : Derives Γ (binaryData kind w b f h x y n)) :
    Derives Γ (binary kind w b f h n) := by
  apply Derives.conjI hc
  apply Derives.exI x
  apply Derives.exI y
  simpa only [binaryBody, Formula.instantiate, binaryData_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem eliminate_single {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) (q : Formula m)
    (hs : Derives Γ (single tag advance w b f h n))
    (hc : Derives (Context.add (singleBody tag advance w b f h n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q :=
  .exE (.conjR hs) hc

theorem eliminate_binary {m} {Γ : Context m} (kind : Fin 4) (w b f h n : Fin m) (q : Formula m)
    (hs : Derives Γ (binary kind w b f h n))
    (hc : Derives (Context.add (binaryBody kind w b f h n) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE (.conjR hs)
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.SyntaxLogicalSyntax
