import PPAC.Migration.Internal.SyntaxIdentityLift

/-! 公式恒等的四内部参数成员归纳合同；IdCode是真实恒等图的原自然码。 -/
namespace PPAC.Migration.Internal.SyntaxRenameIdentitySyntax
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxIdentityMapSyntax
open SyntaxRenameJudgmentSyntax FormulaCodeSyntax

def input {m} (w R S a b n : Fin m) : Formula m := (formulaCode w n a b).conj ((identityCode w a R).conj (identityCode w b S))

def self {m} (w R S a b n : Fin m) : Formula m := renamed w R S a b a b n n

def property {m} (w n : Fin m) : Formula m := .all (.all (.all (.all
  ((input w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc).imp
   (self w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc)))))

def earlier {m} (w n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))

theorem input_rename {m k} (w R S a b n : Fin m) (ρ : Fin m → Fin k) :
    (input w R S a b n).rename ρ = input (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ n) := by
  simp only [input, Formula.rename, formulaCode_rename, identityCode_rename]

theorem self_rename {m k} (w R S a b n : Fin m) (ρ : Fin m → Fin k) :
    (self w R S a b n).rename ρ = self (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ n) := renamed_rename w R S a b a b n n ρ

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property, Formula.rename, input_rename, self_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_at {m} {Γ : Context m} (w n R S a b : Fin m) (hp : Derives Γ (property w n)) :
    Derives Γ ((input w R S a b n).imp (self w R S a b n)) := by
  have hh := Derives.allE b (Derives.allE a (Derives.allE S (Derives.allE R hp)))
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, input_rename, self_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (he : Derives Γ (earlier w n))
    (hw : Derives Γ (.mem x w)) (hx : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hi : Derives Γ (((Formula.mem x w).conj (.mem x n)).imp (property w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x he)
  exact .impE hi (.conjI hw hx)

theorem child {m} {Γ : Context m} (w n x R S a b : Fin m) (he : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x n)) (hc : Derives Γ (formulaCode w x a b))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S)) : Derives Γ (self w R S a b x) :=
  .impE (property_at w x R S a b (earlier_at w n x he (.conjL (FormulaCodeProperties.guards w x a b hc)) hx)) (.conjI hc (.conjI hr hs))
end PPAC.Migration.Internal.SyntaxRenameIdentitySyntax
