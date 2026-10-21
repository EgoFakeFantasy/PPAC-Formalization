import PPAC.Migration.Internal.FormulaCodeTypedFields

/-! 已知原构造及任意同根真实Shape下，父FormulaCode精确等价于完整字段图的原类型检查。 -/
namespace PPAC.Migration.Internal.FormulaCodeGraphTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax SyntaxAtomSyntax
open SyntaxLogicalSyntax (singleCode binaryCode binaryTag quantifierTag)
open FormulaCodeSyntax FormulaCodeTypedFields FormulaCodeBranchSyntax
open StructuralTreeOperatorSyntax (shape)
open FormulaCodeCongruence (conj_congr)
open SyntaxTypeLocalTransfer (iff_refl iff_trans)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def memberCheck {m} (w g b f : Fin m) : Formula m :=
  (zeroField w g 0).conj ((termField w g 1 b f).conj (termField w g 2 b f))
def equalCheck {m} (w g b f : Fin m) : Formula m :=
  (termField w g 0 b f).conj (termField w g 1 b f)
def singleCheck {m} (advance : Bool) (w g b f : Fin m) : Formula m :=
  (contexts w b f).conj (if advance then advancedField w g 0 b f else codeField w g 0 b f)
def binaryCheck {m} (w g b f : Fin m) : Formula m :=
  (contexts w b f).conj ((codeField w g 0 b f).conj (codeField w g 1 b f))

theorem memberCheck_rename {m n} (w g b f : Fin m) (r : Fin m → Fin n) :
    (memberCheck w g b f).rename r = memberCheck (r w) (r g) (r b) (r f) := by
  simp only [memberCheck, Formula.rename, zeroField_rename, termField_rename]
theorem equalCheck_rename {m n} (w g b f : Fin m) (r : Fin m → Fin n) :
    (equalCheck w g b f).rename r = equalCheck (r w) (r g) (r b) (r f) := by
  simp only [equalCheck, Formula.rename, termField_rename]
theorem singleCheck_rename {m n} (advance : Bool) (w g b f : Fin m) (r : Fin m → Fin n) :
    (singleCheck advance w g b f).rename r = singleCheck advance (r w) (r g) (r b) (r f) := by
  cases advance <;> simp only [singleCheck, Bool.false_eq_true, ↓reduceIte, Formula.rename,
    contexts_rename, advancedField_rename, codeField_rename]
theorem binaryCheck_rename {m n} (w g b f : Fin m) (r : Fin m → Fin n) :
    (binaryCheck w g b f).rename r = binaryCheck (r w) (r g) (r b) (r f) := by
  simp only [binaryCheck, Formula.rename, contexts_rename, codeField_rename]

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f s x y t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (memberCheck w g b f)) := by
  have h0 := zero_iff hZ 3 2 w (three s x y) n t p l g 0 hw hc hs
  have h1 := term_iff hZ 3 2 w (three s x y) n t p l g b f 1 hw hc hs
  have h2 := term_iff hZ 3 2 w (three s x y) n t p l g b f 2 hw hc hs
  have hh : Derives Γ ((memberCheck w g b f).iff (memberTypes w b f s x y)) := conj_congr h0 (conj_congr h1 h2)
  exact iff_trans (FormulaCodeKnownAtomic.member_iff hZ w b f s x y n hw hc) (.conjI (.conjR hh) (.conjL hh))

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f x y t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (equalCheck w g b f)) := by
  have h0 := term_iff hZ 2 3 w (two x y) n t p l g b f 0 hw hc hs
  have h1 := term_iff hZ 2 3 w (two x y) n t p l g b f 1 hw hc hs
  have hh : Derives Γ ((equalCheck w g b f).iff (equalTypes w b f x y)) := conj_congr h0 h1
  exact iff_trans (FormulaCodeKnownAtomic.equal_iff hZ w b f x y n hw hc) (.conjI (.conjR hh) (.conjL hh))

theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f x t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode 4 w x n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (singleCheck false w g b f)) := by
  have h0 := code_iff hZ 1 4 w (fun _ => x) n t p l g b f 0 hw hc hs
  have hh : Derives Γ ((singleCheck false w g b f).iff (singleTypes false w b f x)) := conj_congr (iff_refl _) h0
  exact iff_trans (FormulaCodeKnownLogical.negation_iff hZ w b f x n hw hc) (.conjI (.conjR hh) (.conjL hh))

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n b f x y t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (binaryCheck w g b f)) := by
  have h0 := code_iff hZ 2 (binaryTag kind) w (two x y) n t p l g b f 0 hw hc hs
  have h1 := code_iff hZ 2 (binaryTag kind) w (two x y) n t p l g b f 1 hw hc hs
  have hh : Derives Γ ((binaryCheck w g b f).iff (binaryTypes w b f x y)) := conj_congr (iff_refl _) (conj_congr h0 h1)
  have hp : Derives Γ ((formulaCode w n b f).iff (binaryTypes w b f x y)) := by
    have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact FormulaCodeKnownLogical.binary0_iff hZ w b f x y n hw hc
    · exact FormulaCodeKnownLogical.binary1_iff hZ w b f x y n hw hc
    · exact FormulaCodeKnownLogical.binary2_iff hZ w b f x y n hw hc
    · exact FormulaCodeKnownLogical.binary3_iff hZ w b f x y n hw hc
  exact iff_trans hp (.conjI (.conjR hh) (.conjL hh))

theorem quantifier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w n b f x t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode (quantifierTag universal) w x n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ ((formulaCode w n b f).iff (singleCheck true w g b f)) := by
  have h0 := advanced_iff hZ 1 (quantifierTag universal) w (fun _ => x) n t p l g b f 0 hw hc hs
  have hh : Derives Γ ((singleCheck true w g b f).iff (singleTypes true w b f x)) := conj_congr (iff_refl _) h0
  have hp : Derives Γ ((formulaCode w n b f).iff (singleTypes true w b f x)) := by
    cases universal
    · exact FormulaCodeKnownLogical.exists_iff hZ w b f x n hw hc
    · exact FormulaCodeKnownLogical.forall_iff hZ w b f x n hw hc
  exact iff_trans hp (.conjI (.conjR hh) (.conjL hh))

theorem quantifier_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w n b f x t p l g u : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode (quantifierTag universal) w x n))
    (hs : Derives Γ (shape w n t p l g)) (hu : Derives Γ (successor u b)) :
    Derives Γ ((formulaCode w n b f).iff ((contexts w b f).conj (codeField w g 0 u f))) := by
  have h0 := code_iff hZ 1 (quantifierTag universal) w (fun _ => x) n t p l g u f 0 hw hc hs
  have hh := conj_congr (iff_refl (contexts w b f)) h0
  exact iff_trans (FormulaCodeKnownLogical.quantified_iff hZ universal w b f x n u hw hc hu) (.conjI (.conjR hh) (.conjL hh))
end PPAC.Migration.Internal.FormulaCodeGraphTyping
