import PPAC.Migration.Internal.SyntaxRenameTargetFields
import PPAC.Migration.Internal.SyntaxBinderBlock

/-! 全公式复合的14内部参数性质；图/码及全部作用域、两阶段目标均在对象量化内。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxComposeCodeSyntax SyntaxRenameJudgmentSyntax

def input {m} (w R S T U K L a b c d e f n q v : Fin m) : Formula m :=
  (coded w a c e R T K).conj ((coded w b d f S U L).conj
    ((renamed w R S a b c d n q).conj (renamed w T U c d e f q v)))

def result {m} (w K L a b e f n v : Fin m) : Formula m := renamed w K L a b e f n v

def property {m} (w n : Fin m) : Formula m := .all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all (.all ((input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+9)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+10)).castSucc.castSucc.castSucc (Fin.last (m+11)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+12)).castSucc (Fin.last (m+13))).imp (result w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+10)).castSucc.castSucc.castSucc (Fin.last (m+11)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+13)))))))))))))))))

def earlier {m} (w n : Fin m) : Formula m := .all (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))

theorem input_rename {m k} (w R S T U K L a b c d e f n q v : Fin m) (ρ : Fin m → Fin k) :
    (input w R S T U K L a b c d e f n q v).rename ρ = input (ρ w) (ρ R) (ρ S) (ρ T) (ρ U) (ρ K) (ρ L) (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) (ρ n) (ρ q) (ρ v) := by
  simp only [input, Formula.rename, coded_rename, renamed_rename]

theorem result_rename {m k} (w K L a b e f n v : Fin m) (ρ : Fin m → Fin k) :
    (result w K L a b e f n v).rename ρ = result (ρ w) (ρ K) (ρ L) (ρ a) (ρ b) (ρ e) (ρ f) (ρ n) (ρ v) := by
  simp only [result, renamed_rename]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property, Formula.rename, input_rename, result_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_at {m} {Γ : Context m} (w n R S T U K L a b c d e f q v : Fin m) (hp : Derives Γ (property w n)) :
    Derives Γ ((input w R S T U K L a b c d e f n q v).imp (result w K L a b e f n v)) := by
  let P : Formula (m+14) := (input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+9)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+10)).castSucc.castSucc.castSucc (Fin.last (m+11)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+12)).castSucc (Fin.last (m+13))).imp (result w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+10)).castSucc.castSucc.castSucc (Fin.last (m+11)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+13)))
  let ρ : Fin (m+14) → Fin m := Fin.lastCases v (Fin.lastCases q (Fin.lastCases f (Fin.lastCases e (Fin.lastCases d (Fin.lastCases c (Fin.lastCases b (Fin.lastCases a (Fin.lastCases L (Fin.lastCases K (Fin.lastCases U (Fin.lastCases T (Fin.lastCases S (Fin.lastCases R (id))))))))))))))
  have hf : ∀ i : Fin m, ρ (i.castAdd 14) = i := by
    intro i
    change ρ i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = i
    simp only [ρ, Fin.lastCases_castSucc, id_eq]
  have hh := SyntaxBinderBlock.eliminate P ρ hf hp
  exact of_eq (by simp only [P, Formula.rename, input_rename, result_rename, ρ, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (he : Derives Γ (earlier w n)) (hw : Derives Γ (.mem x w)) (hx : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hi : Derives Γ (((Formula.mem x w).conj (.mem x n)).imp (property w x)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x he)
  exact .impE hi (.conjI hw hx)

theorem child {m} {Γ : Context m} (w n x R S T U K L a b c d e f X Z : Fin m)
    (he : Derives Γ (earlier w n)) (hx : Derives Γ (.mem x n))
    (hb : Derives Γ (coded w a c e R T K)) (hf : Derives Γ (coded w b d f S U L))
    (h1 : Derives Γ (renamed w R S a b c d x X)) (h2 : Derives Γ (renamed w T U c d e f X Z)) : Derives Γ (result w K L a b e f x Z) :=
  .impE (property_at w x R S T U K L a b c d e f X Z (earlier_at w n x he (.conjL h1) hx)) (.conjI hb (.conjI hf (.conjI h1 h2)))
end PPAC.Migration.Internal.SyntaxFormulaComposeSyntax
