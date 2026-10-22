import PPAC.Migration.Internal.SyntaxTermImageSyntax

/-! 全内部混合项替换：源变量类别只选实际表，不限制目标项的bound/free类别。 -/
namespace PPAC.Migration.Internal.SyntaxMixedTermSyntax
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxVariableSyntax SyntaxTermSyntax SyntaxTermImageSyntax

def branchBody {m} (bound : Bool) (w f a n q : Fin m) : Formula (m+1) :=
  (Formula.mem (Fin.last m) a.castSucc).conj
    ((code bound w.castSucc (Fin.last m) n.castSucc).conj (edge f.castSucc (Fin.last m) q.castSucc))

def branch {m} (bound : Bool) (w f a n q : Fin m) : Formula m := .ex (branchBody bound w f a n q)

def substituted {m} (w r s a b c d n q : Fin m) : Formula m := (maps w r s a b c d).conj
  ((branch true w r a n q).disj (branch false w s b n q))

def input {m} (w r s a b c d n : Fin m) : Formula m :=
  (maps w r s a b c d).conj (term w a b n)

def existsOutput {m} (w r s a b c d n : Fin m) : Formula m := .ex
  (substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))

def uniqueOutput {m} (w r s a b c d n q : Fin m) : Formula m := .all
  ((substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).imp
    (.equal (Fin.last m) q.castSucc))

def fiber {m} (w r s a b c d n : Fin m) : Formula m := .ex
  ((substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)))

theorem branch_rename {m k} (bound : Bool) (w f a n q : Fin m) (ρ : Fin m → Fin k) :
    (branch bound w f a n q).rename ρ = branch bound (ρ w) (ρ f) (ρ a) (ρ n) (ρ q) := by
  simp only [branch, branchBody, Formula.rename, code_rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem substituted_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (substituted w r s a b c d n q).rename ρ = substituted (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [substituted, Formula.rename, maps_rename, branch_rename]

theorem input_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (input w r s a b c d n).rename ρ = input (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [input, Formula.rename, maps_rename, term_rename]

theorem existsOutput_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (existsOutput w r s a b c d n).rename ρ = existsOutput (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [existsOutput, Formula.rename, substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w r s a b c d n q).rename ρ = uniqueOutput (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w r s a b c d n).rename ρ = fiber (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, substituted_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_branch {m} {Γ : Context m} (bound : Bool) (w f a n q i : Fin m)
    (hi : Derives Γ (.mem i a)) (hc : Derives Γ (code bound w i n)) (he : Derives Γ (edge f i q)) :
    Derives Γ (branch bound w f a n q) := by
  apply Derives.exI i
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [branchBody, Formula.instantiate, Formula.rename, code_rename, edge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hi (.conjI hc he))

theorem intro_substituted {m} {Γ : Context m} (bound : Bool) (w r s a b c d n q : Fin m)
    (hm : Derives Γ (maps w r s a b c d))
    (hb : Derives Γ (branch bound w (SyntaxIndexMapSyntax.selectMap bound r s) (limit bound a b) n q)) :
    Derives Γ (substituted w r s a b c d n q) := by
  cases bound
  · exact .conjI hm (.disjR hb)
  · exact .conjI hm (.disjL hb)

theorem intro_exists {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hq : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (existsOutput w r s a b c d n) := by
  apply Derives.exI q
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, substituted_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

end PPAC.Migration.Internal.SyntaxMixedTermSyntax
