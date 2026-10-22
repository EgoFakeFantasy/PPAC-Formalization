import PPAC.Migration.Internal.SyntaxFormulaComposeSyntax

/-! 同一两阶段复合的六幅实际图与六个原自然码；参数和图均为内部对象。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeDiagrams
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

def diagrams {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : Formula m := (SyntaxComposeSyntax.composed w r t a c e g).conj ((SyntaxComposeSyntax.composed w s u b d f h).conj ((SyntaxMapCodeSyntax.encoded w r a c R).conj ((SyntaxMapCodeSyntax.encoded w s b d S).conj ((SyntaxMapCodeSyntax.encoded w t c e T).conj ((SyntaxMapCodeSyntax.encoded w u d f U).conj ((SyntaxMapCodeSyntax.encoded w g a e K).conj (SyntaxMapCodeSyntax.encoded w h b f L)))))))

theorem diagrams_rename {m k} (w R S T U K L r s t u g h a b c d e f : Fin m) (ρ : Fin m → Fin k) :
    (diagrams w R S T U K L r s t u g h a b c d e f).rename ρ = diagrams (ρ w) (ρ R) (ρ S) (ρ T) (ρ U) (ρ K) (ρ L) (ρ r) (ρ s) (ρ t) (ρ u) (ρ g) (ρ h) (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) := by
  simp only [diagrams, Formula.rename, SyntaxComposeSyntax.composed_rename, SyntaxMapCodeSyntax.encoded_rename]

theorem bound {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxComposeSyntax.composed w r t a c e g) := .conjL (hd)

theorem free {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxComposeSyntax.composed w s u b d f h) := .conjL (.conjR (hd))

theorem encoded_r {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R) := .conjL (.conjR (.conjR (hd)))

theorem encoded_s {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S) := .conjL (.conjR (.conjR (.conjR (hd))))

theorem encoded_t {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.encoded w t c e T) := .conjL (.conjR (.conjR (.conjR (.conjR (hd)))))

theorem encoded_u {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.encoded w u d f U) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (hd))))))

theorem encoded_g {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.encoded w g a e K) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hd)))))))

theorem encoded_h {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.encoded w h b f L) := .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hd)))))))

theorem bound_code {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxComposeCodeSyntax.coded w a c e R T K) :=
  SyntaxComposeCodeSyntax.intro_code w a c e R T K r t g (encoded_r w R S T U K L r s t u g h a b c d e f hd) (encoded_t w R S T U K L r s t u g h a b c d e f hd) (bound w R S T U K L r s t u g h a b c d e f hd) (encoded_g w R S T U K L r s t u g h a b c d e f hd)

theorem free_code {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxComposeCodeSyntax.coded w b d f S U L) :=
  SyntaxComposeCodeSyntax.intro_code w b d f S U L s u h (encoded_s w R S T U K L r s t u g h a b c d e f hd) (encoded_u w R S T U K L r s t u g h a b c d e f hd) (free w R S T U K L r s t u g h a b c d e f hd) (encoded_h w R S T U K L r s t u g h a b c d e f hd)

theorem map_R {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.mapCode w a c R) :=
  SyntaxMapCodeSyntax.intro_code w r a c R (encoded_r w R S T U K L r s t u g h a b c d e f hd)

theorem map_S {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.mapCode w b d S) :=
  SyntaxMapCodeSyntax.intro_code w s b d S (encoded_s w R S T U K L r s t u g h a b c d e f hd)

theorem map_T {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.mapCode w c e T) :=
  SyntaxMapCodeSyntax.intro_code w t c e T (encoded_t w R S T U K L r s t u g h a b c d e f hd)

theorem map_U {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.mapCode w d f U) :=
  SyntaxMapCodeSyntax.intro_code w u d f U (encoded_u w R S T U K L r s t u g h a b c d e f hd)

theorem map_K {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.mapCode w a e K) :=
  SyntaxMapCodeSyntax.intro_code w g a e K (encoded_g w R S T U K L r s t u g h a b c d e f hd)

theorem map_L {m} {Γ : Context m} (w R S T U K L r s t u g h a b c d e f : Fin m) (hd : Derives Γ (diagrams w R S T U K L r s t u g h a b c d e f)) : Derives Γ (SyntaxMapCodeSyntax.mapCode w b f L) :=
  SyntaxMapCodeSyntax.intro_code w h b f L (encoded_h w R S T U K L r s t u g h a b c d e f hd)
end PPAC.Migration.Internal.SyntaxFormulaComposeDiagrams
