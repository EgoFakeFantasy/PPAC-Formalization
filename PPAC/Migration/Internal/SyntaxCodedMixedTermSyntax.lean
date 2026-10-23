import PPAC.Migration.Internal.SyntaxMixedImageCodePairs

/-! 以原数值列表环境参数化的纯混合项替换；实际解码图在对象量词内，不抽取宿主数据。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax

def body {m} (w R S a b c d n q : Fin m) : Formula (m+2) :=
  (SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc).conj
    (SyntaxMixedTermSyntax.substituted w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc)

def substituted {m} (w R S a b c d n q : Fin m) : Formula m := .ex (.ex (body w R S a b c d n q))

def input {m} (w R S a b c d n : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termLists w a b c d R S).conj (SyntaxTermSyntax.term w a b n)

def existsOutput {m} (w R S a b c d n : Fin m) : Formula m := .ex (substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))

def uniqueOutput {m} (w R S a b c d n q : Fin m) : Formula m := .all
  ((substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def fiber {m} (w R S a b c d n : Fin m) : Formula m := .ex
  ((substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj (uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)))

theorem substituted_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (substituted w R S a b c d n q).rename ρ = substituted (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [substituted, body, Formula.rename, SyntaxMixedImageCodeSyntax.encodings_rename, SyntaxMixedTermSyntax.substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem input_rename {m k} (w R S a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (input w R S a b c d n).rename ρ = input (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [input, Formula.rename, SyntaxMixedImageCodeSyntax.termLists_rename, SyntaxTermSyntax.term_rename]

theorem existsOutput_rename {m k} (w R S a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (existsOutput w R S a b c d n).rename ρ = existsOutput (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [existsOutput, Formula.rename, substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m k} (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w R S a b c d n q).rename ρ = uniqueOutput (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w R S a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w R S a b c d n).rename ρ = fiber (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, substituted_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_substituted {m} {Γ : Context m} (w R S a b c d n q r s : Fin m)
    (he : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S))
    (hq : Derives Γ (SyntaxMixedTermSyntax.substituted w r s a b c d n q)) : Derives Γ (substituted w R S a b c d n q) := by
  apply Derives.exI r
  apply Derives.exI s
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, SyntaxMixedImageCodeSyntax.encodings_rename,
    SyntaxMixedTermSyntax.substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he hq)

theorem intro_exists {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hq : Derives Γ (substituted w R S a b c d n q)) : Derives Γ (existsOutput w R S a b c d n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

end PPAC.Migration.Internal.SyntaxCodedMixedTermSyntax
