import PPAC.Migration.Internal.OriginalFreeImageConversion

/-! 原mode0／3的量词可提升环境：自由变量像表使用实际codeConversion，深度与绑定变量界独立。 -/
namespace PPAC.Migration.Internal.OriginalOperationFrameSyntax
open Source SourceAlgebra SourceLogic

def parameter {m} (three : Bool) (P S : Fin m) : Fin m := if three then S else P

theorem parameter_map {m j} (three : Bool) (P S : Fin m) (ρ : Fin m → Fin j) :
    ρ (parameter three P S) = parameter three (ρ P) (ρ S) := by cases three <;> rfl

def modeGuard {m} (three : Bool) (w b c J : Fin m) : Formula m :=
  if three then .equal w w else SyntaxFreeShiftSyntax.shiftCode w b c J

theorem modeGuard_rename {m j} (three : Bool) (w b c J : Fin m) (ρ : Fin m → Fin j) :
    (modeGuard three w b c J).rename ρ = modeGuard three (ρ w) (ρ b) (ρ c) (ρ J) := by
  cases three <;> simp only [modeGuard, Bool.false_eq_true, ↓reduceIte, Formula.rename, SyntaxFreeShiftSyntax.shiftCode_rename]

def frame {m} (three : Bool) (w mode depth P a b c I J R S : Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).conj
    ((OriginalTermTraceSyntax.metadata w depth (parameter three P S)).conj
      ((SyntaxIdentityMapSyntax.identityCode w a I).conj
        ((SyntaxFreeSubstSyntax.codeConversion w b c S J).conj
          ((IndexTermImageCodeSyntax.converted true w I R a a c).conj (modeGuard three w b c J)))))

theorem frame_rename {m j} (three : Bool) (w mode depth P a b c I J R S : Fin m) (ρ : Fin m → Fin j) :
    (frame three w mode depth P a b c I J R S).rename ρ = frame three (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S) := by
  simp only [frame, Formula.rename, SyntaxNumeralSyntax.numeral_rename, OriginalTermTraceSyntax.metadata_rename, parameter_map, SyntaxIdentityMapSyntax.identityCode_rename, SyntaxFreeSubstSyntax.codeConversion_rename, IndexTermImageCodeSyntax.converted_rename, modeGuard_rename]

theorem intro_frame {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth (parameter three P S)))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hf : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b c S J))
    (hb : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (hg : Derives Γ (modeGuard three w b c J)) : Derives Γ (frame three w mode depth P a b c I J R S) :=
  .conjI hm (.conjI hd (.conjI hi (.conjI hf (.conjI hb hg))))

theorem mode_number {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := (.conjL hF)

theorem metadata {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) : Derives Γ (OriginalTermTraceSyntax.metadata w depth (parameter three P S)) := (.conjL (.conjR hF))

theorem identity {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I) := (.conjL (.conjR (.conjR hF)))

theorem free_conversion {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w b c S J) := (.conjL (.conjR (.conjR (.conjR hF))))

theorem bound_conversion {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c) := (.conjL (.conjR (.conjR (.conjR (.conjR hF)))))

theorem guard_data {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S : Fin m)
    (hF : Derives Γ (frame three w mode depth P a b c I J R S)) : Derives Γ (modeGuard three w b c J) := (.conjR (.conjR (.conjR (.conjR (.conjR hF)))))

def liftBody {m} (three : Bool) (w mode _depth P a b c I J _R S A C K H D : Fin m) : Formula (m+1) :=
  (SyntaxMapLiftSyntax.codedLift w.castSucc a.castSucc a.castSucc I.castSucc A.castSucc C.castSucc (Fin.last m)).conj
    ((Formula.equal A.castSucc C.castSucc).conj ((Formula.equal H.castSucc S.castSucc).conj
      (frame three w.castSucc mode.castSucc D.castSucc P.castSucc A.castSucc b.castSucc c.castSucc (Fin.last m) J.castSucc K.castSucc S.castSucc)))

def liftedFrame {m} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) : Formula m :=
  .ex (liftBody three w mode depth P a b c I J R S A C K H D)

theorem liftedFrame_rename {m j} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) (ρ : Fin m → Fin j) :
    (liftedFrame three w mode depth P a b c I J R S A C K H D).rename ρ = liftedFrame three (ρ w) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S) (ρ A) (ρ C) (ρ K) (ρ H) (ρ D) := by
  simp only [liftedFrame, liftBody, Formula.rename, SyntaxMapLiftSyntax.codedLift_rename, frame_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_liftedFrame {m} {Γ : Context m} (three : Bool) (w mode depth P a b c I J R S A C K H D M : Fin m)
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a a I A C M))
    (he : Derives Γ ((Formula.equal A C).conj ((Formula.equal H S).conj (frame three w mode D P A b c M J K S)))) :
    Derives Γ (liftedFrame three w mode depth P a b c I J R S A C K H D) := by
  apply Derives.exI M
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [liftBody, Formula.instantiate, Formula.rename, SyntaxMapLiftSyntax.codedLift_rename, frame_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hl he)

end PPAC.Migration.Internal.OriginalOperationFrameSyntax
