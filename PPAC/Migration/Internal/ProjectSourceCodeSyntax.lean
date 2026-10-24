import PPAC.Migration.Internal.ProjectSourceTypeRecursive

/-! 消去额外载体参数的内部公式码关系；所有幂集与类型见证均为对象存在量词。 -/
namespace PPAC.Migration.Internal.ProjectSourceCodeSyntax
open Source SourceAlgebra SourceLogic PowerSetSyntax ProjectSourceTypeJudgmentSyntax

def carrier {m} (w a c : Fin m) : Formula m := (powerOf a w).conj (powerOf c a)
def existsCarrier {m} (w : Fin m) : Formula m := .ex (.ex
  (carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))
def body {m} (w n b f : Fin m) : Formula (m+2) :=
  (carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (typed w.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc)
def sourceCode {m} (w n b f : Fin m) : Formula m := .ex (.ex (body w n b f))

theorem carrier_rename {m k} (w a c : Fin m) (r : Fin m → Fin k) :
    (carrier w a c).rename r = carrier (r w) (r a) (r c) := by
  simp only [carrier, Formula.rename, powerOf_rename]
theorem existsCarrier_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (existsCarrier w).rename r = existsCarrier (r w) := by
  simp only [existsCarrier, Formula.rename, carrier_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem sourceCode_rename {m k} (w n b f : Fin m) (r : Fin m → Fin k) :
    (sourceCode w n b f).rename r = sourceCode (r w) (r n) (r b) (r f) := by
  simp only [sourceCode, body, Formula.rename, carrier_rename, typed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (w a c n b f : Fin m) (hc : Derives Γ (carrier w a c))
    (ht : Derives Γ (typed w c n b f)) : Derives Γ (sourceCode w n b f) := by
  apply Derives.exI a
  apply Derives.exI c
  simp only [body, Formula.instantiate, Formula.rename, carrier_rename, typed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hc ht

theorem eliminate_code {m} {Γ : Context m} (w n b f : Fin m) (q : Formula m)
    (ht : Derives Γ (sourceCode w n b f))
    (hc : Derives (Context.add (body w n b f) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE ht
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.ProjectSourceCodeSyntax
