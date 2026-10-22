import PPAC.Migration.Internal.SyntaxMixedImageHead

/-! 给定目标映射和新头部项码的完整混合binder提升表：新bound0、旧bound后移、free源索引不变。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageLiftSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax

def body {m} (w R S r s a b c d A C n k h : Fin m) : Formula (m+1) :=
  (SyntaxTermImagePushBoth.both w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc d.castSucc r.castSucc s.castSucc a.castSucc b.castSucc (Fin.last m) h.castSucc).conj
    (SyntaxTermImagePrefixSyntax.prefixed w.castSucc (Fin.last m) a.castSucc C.castSucc d.castSucc n.castSucc A.castSucc k.castSucc)

def lifted {m} (w R S r s a b c d A C n k h : Fin m) : Formula m := .ex (body w R S r s a b c d A C n k h)

def tail {m} (w R S r s a b c d A C n k : Fin m) : Formula m := .ex
  (lifted w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc k.castSucc (Fin.last m))

def existsPair {m} (w R S r s a b c d A C n : Fin m) : Formula m := .ex (tail w.castSucc R.castSucc S.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc n.castSucc (Fin.last m))

theorem lifted_rename {m j} (w R S r s a b c d A C n k h : Fin m) (ρ : Fin m → Fin j) :
    (lifted w R S r s a b c d A C n k h).rename ρ = lifted (ρ w) (ρ R) (ρ S) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ n) (ρ k) (ρ h) := by
  simp only [lifted, body, Formula.rename, SyntaxTermImagePushBoth.both_rename, SyntaxTermImagePrefixSyntax.prefixed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem tail_rename {m j} (w R S r s a b c d A C n k : Fin m) (ρ : Fin m → Fin j) :
    (tail w R S r s a b c d A C n k).rename ρ = tail (ρ w) (ρ R) (ρ S) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ n) (ρ k) := by
  simp only [tail, Formula.rename, lifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsPair_rename {m j} (w R S r s a b c d A C n : Fin m) (ρ : Fin m → Fin j) :
    (existsPair w R S r s a b c d A C n).rename ρ = existsPair (ρ w) (ρ R) (ρ S) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ n) := by
  simp only [existsPair, Formula.rename, tail_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_lifted {m} {Γ : Context m} (w R S r s a b c d A C n k h g : Fin m)
    (hb : Derives Γ (SyntaxTermImagePushBoth.both w R S c d C d r s a b g h)) (hp : Derives Γ (SyntaxTermImagePrefixSyntax.prefixed w g a C d n A k)) :
    Derives Γ (lifted w R S r s a b c d A C n k h) := by
  apply Derives.exI g
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, SyntaxTermImagePushBoth.both_rename,
    SyntaxTermImagePrefixSyntax.prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hb hp)

theorem intro_tail {m} {Γ : Context m} (w R S r s a b c d A C n k h : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) : Derives Γ (tail w R S r s a b c d A C n k) := by
  apply Derives.exI h
  exact of_eq (by simp only [Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hl

theorem intro_pair {m} {Γ : Context m} (w R S r s a b c d A C n k h : Fin m)
    (hl : Derives Γ (lifted w R S r s a b c d A C n k h)) : Derives Γ (existsPair w R S r s a b c d A C n) := by
  apply Derives.exI k
  exact of_eq (by simp only [Formula.instantiate, tail_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (intro_tail w R S r s a b c d A C n k h hl)

end PPAC.Migration.Internal.SyntaxMixedImageLiftSyntax
