import PPAC.Migration.Internal.ObjectSyntaxTypeStates

/-! 不含历史参数的全11构造递归判据；量词体显式实际后继bound。 -/
namespace PPAC.Migration.Internal.SyntaxTypeRecursiveSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax SyntaxLogicalSyntax SyntaxAtomSyntax SyntaxTypeJudgmentSyntax

def advancedTyped {m} (w c x b f : Fin m) : Formula m := .ex
  ((successor (Fin.last m) b.castSucc).conj (typed w.castSucc c.castSucc x.castSucc (Fin.last m) f.castSucc))
def stepCheck {m} (advance : Bool) (w c x b f : Fin m) : Formula m :=
  if advance then advancedTyped w c x b f else typed w c x b f
def singleFields {m} (tag : Nat) (advance : Bool) (w c b f x n : Fin m) : Formula m :=
  (singleCode tag w x n).conj ((Formula.mem x n).conj (stepCheck advance w c x b f))
def binaryFields {m} (kind : Fin 4) (w c b f x y n : Fin m) : Formula m :=
  (binaryCode kind w x y n).conj ((Formula.mem x n).conj ((Formula.mem y n).conj
    ((typed w c x b f).conj (typed w c y b f))))
def singleCaseBody {m} (tag : Nat) (advance : Bool) (w c b f n : Fin m) : Formula (m+1) :=
  singleFields tag advance w.castSucc c.castSucc b.castSucc f.castSucc (Fin.last m) n.castSucc
def binaryCaseBody {m} (kind : Fin 4) (w c b f n : Fin m) : Formula (m+2) :=
  binaryFields kind w.castSucc.castSucc c.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc
def singleCase {m} (tag : Nat) (advance : Bool) (w c b f n : Fin m) : Formula m :=
  (contexts w b f).conj (.ex (singleCaseBody tag advance w c b f n))
def binaryCase {m} (kind : Fin 4) (w c b f n : Fin m) : Formula m :=
  (contexts w b f).conj (.ex (.ex (binaryCaseBody kind w c b f n)))
def allCases {m} (w c n b f : Fin m) : Formula m :=
  (atomic w b f n).disj ((singleCase 4 false w c b f n).disj
    ((binaryCase 0 w c b f n).disj ((binaryCase 1 w c b f n).disj
      ((binaryCase 2 w c b f n).disj ((binaryCase 3 w c b f n).disj
        ((singleCase 9 true w c b f n).disj (singleCase 10 true w c b f n)))))))
def criterion {m} (w c n b f : Fin m) : Formula m := (Formula.mem n w).conj (allCases w c n b f)

theorem advancedTyped_rename {m k} (w c x b f : Fin m) (r : Fin m → Fin k) :
    (advancedTyped w c x b f).rename r = advancedTyped (r w) (r c) (r x) (r b) (r f) := by
  simp only [advancedTyped, Formula.rename, successor_rename, typed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem stepCheck_rename {m k} (advance : Bool) (w c x b f : Fin m) (r : Fin m → Fin k) :
    (stepCheck advance w c x b f).rename r = stepCheck advance (r w) (r c) (r x) (r b) (r f) := by
  cases advance <;> simp only [stepCheck, Bool.false_eq_true, ↓reduceIte, advancedTyped_rename, typed_rename]
theorem singleFields_rename {m k} (tag : Nat) (advance : Bool) (w c b f x n : Fin m) (r : Fin m → Fin k) :
    (singleFields tag advance w c b f x n).rename r = singleFields tag advance (r w) (r c) (r b) (r f) (r x) (r n) := by
  simp only [singleFields, Formula.rename, singleCode_rename, stepCheck_rename]
theorem binaryFields_rename {m k} (kind : Fin 4) (w c b f x y n : Fin m) (r : Fin m → Fin k) :
    (binaryFields kind w c b f x y n).rename r = binaryFields kind (r w) (r c) (r b) (r f) (r x) (r y) (r n) := by
  simp only [binaryFields, Formula.rename, binaryCode_rename, typed_rename]
theorem singleCase_rename {m k} (tag : Nat) (advance : Bool) (w c b f n : Fin m) (r : Fin m → Fin k) :
    (singleCase tag advance w c b f n).rename r = singleCase tag advance (r w) (r c) (r b) (r f) (r n) := by
  simp only [singleCase, singleCaseBody, Formula.rename, contexts_rename, singleFields_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem binaryCase_rename {m k} (kind : Fin 4) (w c b f n : Fin m) (r : Fin m → Fin k) :
    (binaryCase kind w c b f n).rename r = binaryCase kind (r w) (r c) (r b) (r f) (r n) := by
  simp only [binaryCase, binaryCaseBody, Formula.rename, contexts_rename, binaryFields_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem allCases_rename {m k} (w c n b f : Fin m) (r : Fin m → Fin k) :
    (allCases w c n b f).rename r = allCases (r w) (r c) (r n) (r b) (r f) := by
  simp only [allCases, Formula.rename, atomic_rename, singleCase_rename, binaryCase_rename]
theorem criterion_rename {m k} (w c n b f : Fin m) (r : Fin m → Fin k) :
    (criterion w c n b f).rename r = criterion (r w) (r c) (r n) (r b) (r f) := by
  simp only [criterion, Formula.rename, allCases_rename]

theorem intro_advanced {m} {Γ : Context m} (w c x b f k : Fin m) (hk : Derives Γ (successor k b))
    (ht : Derives Γ (typed w c x k f)) : Derives Γ (advancedTyped w c x b f) := by
  apply Derives.exI k
  simp only [Formula.instantiate, Formula.rename, successor_rename, typed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hk ht

theorem intro_single {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w c b f x n : Fin m)
    (hc : Derives Γ (contexts w b f)) (hd : Derives Γ (singleFields tag advance w c b f x n)) :
    Derives Γ (singleCase tag advance w c b f n) := by
  apply Derives.conjI hc
  apply Derives.exI x
  simpa only [singleCaseBody, Formula.instantiate, singleFields_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem intro_binary {m} {Γ : Context m} (kind : Fin 4) (w c b f x y n : Fin m)
    (hc : Derives Γ (contexts w b f)) (hd : Derives Γ (binaryFields kind w c b f x y n)) :
    Derives Γ (binaryCase kind w c b f n) := by
  apply Derives.conjI hc
  apply Derives.exI x
  apply Derives.exI y
  simpa only [binaryCaseBody, Formula.instantiate, binaryFields_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hd

theorem eliminate_single {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w c b f n : Fin m) (q : Formula m)
    (hs : Derives Γ (singleCase tag advance w c b f n))
    (hc : Derives (Context.add (singleCaseBody tag advance w c b f n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE (.conjR hs) hc

theorem eliminate_binary {m} {Γ : Context m} (kind : Fin 4) (w c b f n : Fin m) (q : Formula m)
    (hs : Derives Γ (binaryCase kind w c b f n))
    (hc : Derives (Context.add (binaryCaseBody kind w c b f n) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE (.conjR hs)
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.SyntaxTypeRecursiveSyntax
