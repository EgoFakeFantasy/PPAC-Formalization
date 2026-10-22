import PPAC.Migration.Internal.SyntaxMixedImageLiftState
import PPAC.Migration.Internal.SyntaxIdentityUnique

/-! 完全内部化的混合binder关系；目标映射、零和bvar0码均为对象存在见证。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageBinderSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax

def ready {m} (w r s a b c d A C k h R S z n : Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftMap w c C R).conj ((SyntaxIdentityMapSyntax.identityMap w d S).conj
    ((SyntaxMixedImageHead.head w C d z n).conj (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h)))

def body {m} (w r s a b c d A C k h : Fin m) : Formula (m+4) :=
  ready w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def lifted {m} (w r s a b c d A C k h : Fin m) : Formula m := .ex (.ex (.ex (.ex (body w r s a b c d A C k h))))

def tail {m} (w r s a b c d A C k : Fin m) : Formula m := .ex (lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc k.castSucc (Fin.last m))

def existsPair {m} (w r s a b c d A C : Fin m) : Formula m := .ex (tail w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m))

theorem ready_rename {m j} (w r s a b c d A C k h R S z n : Fin m) (ρ : Fin m → Fin j) :
    (ready w r s a b c d A C k h R S z n).rename ρ = ready (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ k) (ρ h) (ρ R) (ρ S) (ρ z) (ρ n) := by
  simp only [ready, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIdentityMapSyntax.identityMap_rename, SyntaxMixedImageHead.head_rename, SyntaxMixedImageLiftSyntax.lifted_rename]

theorem lifted_rename {m j} (w r s a b c d A C k h : Fin m) (ρ : Fin m → Fin j) :
    (lifted w r s a b c d A C k h).rename ρ = lifted (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ k) (ρ h) := by
  simp only [lifted, body, Formula.rename, ready_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem tail_rename {m j} (w r s a b c d A C k : Fin m) (ρ : Fin m → Fin j) :
    (tail w r s a b c d A C k).rename ρ = tail (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ k) := by
  simp only [tail, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsPair_rename {m j} (w r s a b c d A C : Fin m) (ρ : Fin m → Fin j) :
    (existsPair w r s a b c d A C).rename ρ = existsPair (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [existsPair, Formula.rename, tail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_lifted {m} {Γ : Context m} (w r s a b c d A C k h R S z n : Fin m)
    (hr : Derives Γ (ready w r s a b c d A C k h R S z n)) : Derives Γ (lifted w r s a b c d A C k h) := by
  apply Derives.exI R
  apply Derives.exI S
  apply Derives.exI z
  apply Derives.exI n
  exact of_eq (by simp only [body, Formula.instantiate, ready_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr

theorem intro_tail {m} {Γ : Context m} (w r s a b c d A C k h : Fin m)
    (hl : Derives Γ (lifted w r s a b c d A C k h)) : Derives Γ (tail w r s a b c d A C k) := by
  apply Derives.exI h
  exact of_eq (by simp only [Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hl

theorem intro_pair {m} {Γ : Context m} (w r s a b c d A C k h : Fin m)
    (hl : Derives Γ (lifted w r s a b c d A C k h)) : Derives Γ (existsPair w r s a b c d A C) := by
  apply Derives.exI k
  exact of_eq (by simp only [Formula.instantiate, tail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (intro_tail w r s a b c d A C k h hl)

end PPAC.Migration.Internal.SyntaxMixedImageBinderSyntax
