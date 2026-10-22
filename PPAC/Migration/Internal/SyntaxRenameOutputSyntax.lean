import PPAC.Migration.Internal.SyntaxRenameAdvancedKnown

/-! 实际∃!目标码和全内部六参数成员归纳合同；不预设实际唯一输出已经成立。 -/
namespace PPAC.Migration.Internal.SyntaxRenameOutputSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxRenameJudgmentSyntax SyntaxMapCodeSyntax

def input {m} (w r s a b c d n : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n a b).conj ((mapCode w a c r).conj (mapCode w b d s))

def existsOutput {m} (w r s a b c d n : Fin m) : Formula m := .ex
  (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))

def uniqueOutput {m} (w r s a b c d n q : Fin m) : Formula m := .all
  ((renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).imp
    (.equal (Fin.last m) q.castSucc))

def fiber {m} (w r s a b c d n : Fin m) : Formula m := .ex
  ((renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)))

def property {m} (w n : Fin m) : Formula m := .all (.all (.all (.all (.all (.all ((input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).imp (fiber w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)))))))

def earlier {m} (w n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))

theorem input_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (input w r s a b c d n).rename ρ = input (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [input, Formula.rename, FormulaCodeSyntax.formulaCode_rename, mapCode_rename]

theorem existsOutput_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (existsOutput w r s a b c d n).rename ρ = existsOutput (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [existsOutput, Formula.rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m k} (w r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w r s a b c d n q).rename ρ = uniqueOutput (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w r s a b c d n).rename ρ = fiber (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, renamed_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property, Formula.rename, input_rename, fiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_exists {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hr : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (existsOutput w r s a b c d n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr

theorem intro_fiber {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hr : Derives Γ (renamed w r s a b c d n q)) (hu : Derives Γ (uniqueOutput w r s a b c d n q)) :
    Derives Γ (fiber w r s a b c d n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, renamed_rename, uniqueOutput_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hu)

theorem property_at {m} {Γ : Context m} (w n r s a b c d : Fin m) (hp : Derives Γ (property w n)) :
    Derives Γ ((input w r s a b c d n).imp (fiber w r s a b c d n)) := by
  have hh := Derives.allE d (Derives.allE c (Derives.allE b (Derives.allE a (Derives.allE s (Derives.allE r hp)))))
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, input_rename, fiber_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (he : Derives Γ (earlier w n))
    (hw : Derives Γ (.mem x w)) (hx : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hi : Derives Γ (((Formula.mem x w).conj (.mem x n)).imp (property w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x he)
  exact .impE hi (.conjI hw hx)
end PPAC.Migration.Internal.SyntaxRenameOutputSyntax
