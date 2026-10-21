import PPAC.Migration.Internal.ObjectNaturalNumericBounds

/-! 固定原Gödel配数：a∈b时b²+a，否则(a²+a)+b；数值全为对象变量。 -/
namespace PPAC.Migration.Internal.GodelPairSyntax
open Source SourceAlgebra SourceLogic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)

def lowerWitness {m} (w a b p : Fin m) : Formula (m+1) :=
  (product w.castSucc b.castSucc b.castSucc (Fin.last m)).conj (sum w.castSucc (Fin.last m) a.castSucc p.castSucc)
def lower {m} (w a b p : Fin m) : Formula m := .ex (lowerWitness w a b p)
def upperWitness {m} (w a b p : Fin m) : Formula (m+2) :=
  (product w.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc).conj
    ((sum w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1))).conj
      (sum w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc p.castSucc.castSucc))
def upper {m} (w a b p : Fin m) : Formula m := .ex (.ex (upperWitness w a b p))
def code {m} (w a b p : Fin m) : Formula m :=
  ((Formula.mem a b).conj (lower w a b p)).disj ((Formula.mem a b).neg.conj (upper w a b p))
def existsLower {m} (w a b : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (lower w.castSucc a.castSucc b.castSucc (Fin.last m)))
def existsUpper {m} (w a b : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (upper w.castSucc a.castSucc b.castSucc (Fin.last m)))
def existsCode {m} (w a b : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc a.castSucc b.castSucc (Fin.last m)))
def fiber {m} (w a b : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc a.castSucc b.castSucc (Fin.last m))).conj (.all
    ((code w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem lower_rename {m k} (w a b p : Fin m) (r : Fin m → Fin k) :
    (lower w a b p).rename r = lower (r w) (r a) (r b) (r p) := by
  simp only [lower, lowerWitness, Formula.rename, sum_rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem upper_rename {m k} (w a b p : Fin m) (r : Fin m → Fin k) :
    (upper w a b p).rename r = upper (r w) (r a) (r b) (r p) := by
  simp only [upper, upperWitness, Formula.rename, sum_rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem code_rename {m k} (w a b p : Fin m) (r : Fin m → Fin k) :
    (code w a b p).rename r = code (r w) (r a) (r b) (r p) := by
  simp only [code, Formula.rename, Formula.neg, lower_rename, upper_rename]
theorem existsLower_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (existsLower w a b).rename r = existsLower (r w) (r a) (r b) := by
  simp only [existsLower, Formula.rename, lower_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsUpper_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (existsUpper w a b).rename r = existsUpper (r w) (r a) (r b) := by
  simp only [existsUpper, Formula.rename, upper_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsCode_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (existsCode w a b).rename r = existsCode (r w) (r a) (r b) := by
  simp only [existsCode, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiber_rename {m k} (w a b : Fin m) (r : Fin m → Fin k) :
    (fiber w a b).rename r = fiber (r w) (r a) (r b) := by
  simp only [fiber, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_lower {m} {Γ : Context m} (w a b p q : Fin m) (hq : Derives Γ (product w b b q))
    (hp : Derives Γ (sum w q a p)) : Derives Γ (lower w a b p) := by
  apply Derives.exI q
  simp only [Formula.instantiate, lowerWitness, Formula.rename, product_rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hq hp

theorem intro_upper {m} {Γ : Context m} (w a b p q t : Fin m) (hq : Derives Γ (product w a a q))
    (ht : Derives Γ (sum w q a t)) (hp : Derives Γ (sum w t b p)) : Derives Γ (upper w a b p) := by
  apply Derives.exI q
  apply Derives.exI t
  simp only [Formula.instantiate, upperWitness, Formula.rename, product_rename, sum_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hq (.conjI ht hp)

theorem eliminate_lower {m} {Γ : Context m} (w a b p : Fin m) (r : Formula m) (hp : Derives Γ (lower w a b p))
    (hc : Derives (Context.add (lowerWitness w a b p) (Context.image Formula.raise Γ)) r.raise) : Derives Γ r := .exE hp hc

theorem eliminate_upper {m} {Γ : Context m} (w a b p : Fin m) (r : Formula m) (hp : Derives Γ (upper w a b p))
    (hc : Derives (Context.add (upperWitness w a b p) (Context.image Formula.raise (Context.image Formula.raise Γ))) r.raise.raise) : Derives Γ r := by
  change Derives Γ (.ex (.ex (upperWitness w a b p))) at hp
  apply Derives.exE hp
  apply Derives.exE (p := upperWitness w a b p) (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩

theorem intro_existsLower {m} {Γ : Context m} (w a b p : Fin m) (hp : Derives Γ (.mem p w))
    (hc : Derives Γ (lower w a b p)) : Derives Γ (existsLower w a b) := by
  apply Derives.exI p
  simp only [Formula.instantiate, Formula.rename, lower_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hp hc

theorem intro_existsUpper {m} {Γ : Context m} (w a b p : Fin m) (hp : Derives Γ (.mem p w))
    (hc : Derives Γ (upper w a b p)) : Derives Γ (existsUpper w a b) := by
  apply Derives.exI p
  simp only [Formula.instantiate, Formula.rename, upper_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hp hc

theorem intro_existsCode {m} {Γ : Context m} (w a b p : Fin m) (hp : Derives Γ (.mem p w))
    (hc : Derives Γ (code w a b p)) : Derives Γ (existsCode w a b) := by
  apply Derives.exI p
  simp only [Formula.instantiate, Formula.rename, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hp hc
end PPAC.Migration.Internal.GodelPairSyntax
