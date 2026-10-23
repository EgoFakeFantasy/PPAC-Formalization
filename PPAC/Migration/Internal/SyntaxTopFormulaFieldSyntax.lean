import PPAC.Migration.Internal.SyntaxTopFormulaFiber

/-! 首槽公式的原子操作数及量词下实际双表提升查询；环境码仍完全由对象量词绑定。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaFieldSyntax
open Source SourceAlgebra SourceLogic

def instantiateEqualState {m} (w a b A t x y X Y R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).conj (SyntaxMixedFormulaKnownFieldsSyntax.equalOperands w R S A b a b x y X Y)

def instantiateEqualBody {m} (w a b A t x y X Y : Fin m) : Formula (m+2) :=
  instantiateEqualState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def instantiateEqual {m} (w a b A t x y X Y : Fin m) : Formula m := .ex (.ex (instantiateEqualBody w a b A t x y X Y))

theorem instantiateEqualState_rename {m k} (w a b A t x y X Y R S : Fin m) (ρ : Fin m → Fin k) :
    (instantiateEqualState w a b A t x y X Y R S).rename ρ = instantiateEqualState (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ x) (ρ y) (ρ X) (ρ Y) (ρ R) (ρ S) := by
  simp only [instantiateEqualState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaKnownFieldsSyntax.equalOperands_rename]

theorem instantiateEqual_rename {m k} (w a b A t x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (instantiateEqual w a b A t x y X Y).rename ρ = instantiateEqual (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [instantiateEqual, instantiateEqualBody, Formula.rename, instantiateEqualState_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def instantiateMemberState {m} (w a b A t z Z x y X Y R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).conj (SyntaxMixedFormulaKnownFieldsSyntax.memberOperands w R S A b a b z Z x y X Y)

def instantiateMemberBody {m} (w a b A t z Z x y X Y : Fin m) : Formula (m+2) :=
  instantiateMemberState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc z.castSucc.castSucc Z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def instantiateMember {m} (w a b A t z Z x y X Y : Fin m) : Formula m := .ex (.ex (instantiateMemberBody w a b A t z Z x y X Y))

theorem instantiateMemberState_rename {m k} (w a b A t z Z x y X Y R S : Fin m) (ρ : Fin m → Fin k) :
    (instantiateMemberState w a b A t z Z x y X Y R S).rename ρ = instantiateMemberState (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ z) (ρ Z) (ρ x) (ρ y) (ρ X) (ρ Y) (ρ R) (ρ S) := by
  simp only [instantiateMemberState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaKnownFieldsSyntax.memberOperands_rename]

theorem instantiateMember_rename {m k} (w a b A t z Z x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (instantiateMember w a b A t z Z x y X Y).rename ρ = instantiateMember (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ z) (ρ Z) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [instantiateMember, instantiateMemberBody, Formula.rename, instantiateMemberState_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def instantiateAdvancedState {m} (w a b A t x X R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).conj (SyntaxMixedFormulaRecursiveSyntax.advanced w x R S A b a b X)

def instantiateAdvancedBody {m} (w a b A t x X : Fin m) : Formula (m+2) :=
  instantiateAdvancedState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def instantiateAdvanced {m} (w a b A t x X : Fin m) : Formula m := .ex (.ex (instantiateAdvancedBody w a b A t x X))

theorem instantiateAdvancedState_rename {m k} (w a b A t x X R S : Fin m) (ρ : Fin m → Fin k) :
    (instantiateAdvancedState w a b A t x X R S).rename ρ = instantiateAdvancedState (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ x) (ρ X) (ρ R) (ρ S) := by
  simp only [instantiateAdvancedState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaRecursiveSyntax.advanced_rename]

theorem instantiateAdvanced_rename {m k} (w a b A t x X : Fin m) (ρ : Fin m → Fin k) :
    (instantiateAdvanced w a b A t x X).rename ρ = instantiateAdvanced (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ x) (ρ X) := by
  simp only [instantiateAdvanced, instantiateAdvancedBody, Formula.rename, instantiateAdvancedState_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def abstractEqualState {m} (w a b A B x y X Y R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).conj (SyntaxMixedFormulaKnownFieldsSyntax.equalOperands w R S a B A b x y X Y)

def abstractEqualBody {m} (w a b A B x y X Y : Fin m) : Formula (m+2) :=
  abstractEqualState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def abstractEqual {m} (w a b A B x y X Y : Fin m) : Formula m := .ex (.ex (abstractEqualBody w a b A B x y X Y))

theorem abstractEqualState_rename {m k} (w a b A B x y X Y R S : Fin m) (ρ : Fin m → Fin k) :
    (abstractEqualState w a b A B x y X Y R S).rename ρ = abstractEqualState (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ x) (ρ y) (ρ X) (ρ Y) (ρ R) (ρ S) := by
  simp only [abstractEqualState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename, SyntaxMixedFormulaKnownFieldsSyntax.equalOperands_rename]

theorem abstractEqual_rename {m k} (w a b A B x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (abstractEqual w a b A B x y X Y).rename ρ = abstractEqual (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [abstractEqual, abstractEqualBody, Formula.rename, abstractEqualState_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def abstractMemberState {m} (w a b A B z Z x y X Y R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).conj (SyntaxMixedFormulaKnownFieldsSyntax.memberOperands w R S a B A b z Z x y X Y)

def abstractMemberBody {m} (w a b A B z Z x y X Y : Fin m) : Formula (m+2) :=
  abstractMemberState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc Z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def abstractMember {m} (w a b A B z Z x y X Y : Fin m) : Formula m := .ex (.ex (abstractMemberBody w a b A B z Z x y X Y))

theorem abstractMemberState_rename {m k} (w a b A B z Z x y X Y R S : Fin m) (ρ : Fin m → Fin k) :
    (abstractMemberState w a b A B z Z x y X Y R S).rename ρ = abstractMemberState (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ z) (ρ Z) (ρ x) (ρ y) (ρ X) (ρ Y) (ρ R) (ρ S) := by
  simp only [abstractMemberState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename, SyntaxMixedFormulaKnownFieldsSyntax.memberOperands_rename]

theorem abstractMember_rename {m k} (w a b A B z Z x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (abstractMember w a b A B z Z x y X Y).rename ρ = abstractMember (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ z) (ρ Z) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [abstractMember, abstractMemberBody, Formula.rename, abstractMemberState_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

def abstractAdvancedState {m} (w a b A B x X R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).conj (SyntaxMixedFormulaRecursiveSyntax.advanced w x R S a B A b X)

def abstractAdvancedBody {m} (w a b A B x X : Fin m) : Formula (m+2) :=
  abstractAdvancedState w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def abstractAdvanced {m} (w a b A B x X : Fin m) : Formula m := .ex (.ex (abstractAdvancedBody w a b A B x X))

theorem abstractAdvancedState_rename {m k} (w a b A B x X R S : Fin m) (ρ : Fin m → Fin k) :
    (abstractAdvancedState w a b A B x X R S).rename ρ = abstractAdvancedState (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ x) (ρ X) (ρ R) (ρ S) := by
  simp only [abstractAdvancedState, Formula.rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename, SyntaxMixedFormulaRecursiveSyntax.advanced_rename]

theorem abstractAdvanced_rename {m k} (w a b A B x X : Fin m) (ρ : Fin m → Fin k) :
    (abstractAdvanced w a b A B x X).rename ρ = abstractAdvanced (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ x) (ρ X) := by
  simp only [abstractAdvanced, abstractAdvancedBody, Formula.rename, abstractAdvancedState_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.SyntaxTopFormulaFieldSyntax
