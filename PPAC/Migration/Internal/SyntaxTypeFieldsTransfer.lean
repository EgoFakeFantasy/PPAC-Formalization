import PPAC.Migration.Internal.SyntaxTypeReadTransfer

/-! 保留原构造及严格子码界，仅把每个真实历史查询等价迁移为Typed。 -/
namespace PPAC.Migration.Internal.SyntaxTypeFieldsTransfer
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTypeRecursionSyntax SyntaxLogicalSyntax SyntaxTypeRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w c b f h x n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n))
    (hd : Derives Γ (singleData tag advance w b f h x n)) : Derives Γ (singleFields tag advance w c b f x n) := by
  have hh := SyntaxTypeReadTransfer.check_iff hZ advance w c h n x b f hw hn (.conjL (.conjR hd)) hg
  exact .conjI (.conjL hd) (.conjI (.conjL (.conjR hd)) (.impE (.conjL hh) (.conjR (.conjR hd))))

theorem single_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w c b f h x n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n))
    (hd : Derives Γ (singleFields tag advance w c b f x n)) : Derives Γ (singleData tag advance w b f h x n) := by
  have hh := SyntaxTypeReadTransfer.check_iff hZ advance w c h n x b f hw hn (.conjL (.conjR hd)) hg
  exact .conjI (.conjL hd) (.conjI (.conjL (.conjR hd)) (.impE (.conjR hh) (.conjR (.conjR hd))))

theorem binary_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w c b f h x y n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n))
    (hd : Derives Γ (binaryData kind w b f h x y n)) : Derives Γ (binaryFields kind w c b f x y n) := by
  have hx := SyntaxTypeReadTransfer.plain hZ w c h n x b f hw hn (.conjL (.conjR hd)) hg
  have hy := SyntaxTypeReadTransfer.plain hZ w c h n y b f hw hn (.conjL (.conjR (.conjR hd))) hg
  exact .conjI (.conjL hd) (.conjI (.conjL (.conjR hd)) (.conjI (.conjL (.conjR (.conjR hd)))
    (.conjI (.impE (.conjL hx) (.conjL (.conjR (.conjR (.conjR hd)))))
      (.impE (.conjL hy) (.conjR (.conjR (.conjR (.conjR hd))))))))

theorem binary_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w c b f h x y n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n))
    (hd : Derives Γ (binaryFields kind w c b f x y n)) : Derives Γ (binaryData kind w b f h x y n) := by
  have hx := SyntaxTypeReadTransfer.plain hZ w c h n x b f hw hn (.conjL (.conjR hd)) hg
  have hy := SyntaxTypeReadTransfer.plain hZ w c h n y b f hw hn (.conjL (.conjR (.conjR hd))) hg
  exact .conjI (.conjL hd) (.conjI (.conjL (.conjR hd)) (.conjI (.conjL (.conjR (.conjR hd)))
    (.conjI (.impE (.conjR hx) (.conjL (.conjR (.conjR (.conjR hd)))))
      (.impE (.conjR hy) (.conjR (.conjR (.conjR (.conjR hd))))))))
end PPAC.Migration.Internal.SyntaxTypeFieldsTransfer
