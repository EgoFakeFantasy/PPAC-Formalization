import PPAC.Migration.Internal.SyntaxCodedMixedTermFields

/-! 原数值混合环境码的binder提升；四个实际输入/输出图均为对象存在见证。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax

def state {m} (w R S a b c d A C K H r s k h : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S).conj
    ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).conj
      (SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H))

def body {m} (w R S a b c d A C K H : Fin m) : Formula (m+4) := state w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc
  (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def lifted {m} (w R S a b c d A C K H : Fin m) : Formula m := .ex (.ex (.ex (.ex (body w R S a b c d A C K H))))

def input {m} (w R S a b c d A C : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termLists w a b c d R S).conj ((successor A a).conj (successor C c))

def tail {m} (w R S a b c d A C K : Fin m) : Formula m := .ex
  (lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc (Fin.last m))

def existsPair {m} (w R S a b c d A C : Fin m) : Formula m := .ex
  (tail w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m))

theorem state_rename {m j} (w R S a b c d A C K H r s k h : Fin m) (ρ : Fin m → Fin j) :
    (state w R S a b c d A C K H r s k h).rename ρ = state (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ K) (ρ H) (ρ r) (ρ s) (ρ k) (ρ h) := by
  simp only [state, Formula.rename, SyntaxMixedImageCodeSyntax.encodings_rename, SyntaxMixedImageBinderSyntax.lifted_rename]

theorem lifted_rename {m j} (w R S a b c d A C K H : Fin m) (ρ : Fin m → Fin j) :
    (lifted w R S a b c d A C K H).rename ρ = lifted (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ K) (ρ H) := by
  simp only [lifted, body, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem input_rename {m j} (w R S a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (input w R S a b c d A C).rename ρ = input (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [input, Formula.rename, SyntaxMixedImageCodeSyntax.termLists_rename, successor_rename]

theorem tail_rename {m j} (w R S a b c d A C K : Fin m) (ρ : Fin m → Fin j) :
    (tail w R S a b c d A C K).rename ρ = tail (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ K) := by
  simp only [tail, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsPair_rename {m j} (w R S a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (existsPair w R S a b c d A C).rename ρ = existsPair (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [existsPair, Formula.rename, tail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_lifted {m} {Γ : Context m} (w R S a b c d A C K H r s k h : Fin m)
    (hb : Derives Γ (state w R S a b c d A C K H r s k h)) : Derives Γ (lifted w R S a b c d A C K H) := by
  apply Derives.exI r
  apply Derives.exI s
  apply Derives.exI k
  apply Derives.exI h
  exact of_eq (by simp only [body, Formula.instantiate, state_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb

theorem intro_tail {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hb : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (tail w R S a b c d A C K) := by
  apply Derives.exI H
  exact of_eq (by simp only [Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb

theorem intro_pair {m} {Γ : Context m} (w R S a b c d A C K H : Fin m)
    (hb : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (existsPair w R S a b c d A C) := by
  apply Derives.exI K
  exact of_eq (by simp only [Formula.instantiate, tail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_tail w R S a b c d A C K H hb)

end PPAC.Migration.Internal.SyntaxCodedMixedBinderSyntax
