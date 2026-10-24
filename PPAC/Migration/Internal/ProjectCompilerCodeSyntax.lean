import PPAC.Migration.Internal.ProjectCompilerJudgment

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerCodeSyntax
open Source SourceAlgebra SourceLogic PowerSetSyntax ProjectCompilerJudgmentSyntax

def carrier {m} (w a c : Fin m) : Formula m := (powerOf a w).conj (powerOf c a)
def existsCarrier {m} (w : Fin m) : Formula m := .ex (.ex
  (carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))
def body {m} (w n b f : Fin m) : Formula (m+2) :=
  (carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (atCarrier w.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc)
def compiled {m} (w n b f : Fin m) : Formula m := .ex (.ex (body w n b f))

theorem carrier_rename {m k} (w a c : Fin m) (r : Fin m → Fin k) :
    (carrier w a c).rename r = carrier (r w) (r a) (r c) := by
  simp only [carrier, Formula.rename, powerOf_rename]
theorem existsCarrier_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (existsCarrier w).rename r = existsCarrier (r w) := by
  simp only [existsCarrier, Formula.rename, carrier_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem compiled_rename {m k} (w n b f : Fin m) (r : Fin m → Fin k) :
    (compiled w n b f).rename r = compiled (r w) (r n) (r b) (r f) := by
  simp only [compiled, body, Formula.rename, carrier_rename, atCarrier_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (w a c n b f : Fin m) (hc : Derives Γ (carrier w a c))
    (ht : Derives Γ (atCarrier w c n b f)) : Derives Γ (compiled w n b f) := by
  apply Derives.exI a
  apply Derives.exI c
  simp only [body, Formula.instantiate, Formula.rename, carrier_rename, atCarrier_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hc ht

theorem eliminate_code {m} {Γ : Context m} (w n b f : Fin m) (q : Formula m)
    (ht : Derives Γ (compiled w n b f))
    (hc : Derives (Context.add (body w n b f) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE ht
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.ProjectCompilerCodeSyntax
