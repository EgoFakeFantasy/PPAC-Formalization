import PPAC.Migration.SourceDerivation
import PPAC.Migration.SourceStatements

/-! 固定OpenAI源ZF与目标理论的谓词呈现；全参数Replacement保持原样。 -/
namespace PPAC.Migration.Source.SetLanguage
inductive IsZFAxiom : Sentence → Prop where
  | extensionality : IsZFAxiom extensionality
  | emptySet : IsZFAxiom emptySet
  | pairing : IsZFAxiom pairing
  | union : IsZFAxiom union
  | powerSet : IsZFAxiom powerSet
  | infinity : IsZFAxiom infinity
  | foundation : IsZFAxiom foundation
  | separation {n} (p : Formula (n + 1)) : IsZFAxiom (separation p)
  | replacement {n} (p : Formula (n + 2)) : IsZFAxiom (replacement p)

def ZF : Theory := IsZFAxiom

def targetTheory : Theory := fun p => ZF p ∨ p = PP ∨ p = ACwo ∨ p = AC.neg
end PPAC.Migration.Source.SetLanguage
