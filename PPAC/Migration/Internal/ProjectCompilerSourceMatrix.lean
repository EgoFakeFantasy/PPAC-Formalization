import PPAC.Migration.Internal.ProjectCompilerSourceQueries

/-! Each actual compiler matrix supplies the independent source grammar, without assuming source validity. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceMatrix
open Source SourceAlgebra SourceLogic ProjectCompilerCaseSyntax ProjectCompilerRecursiveSyntax ProjectCompilerSourceSyntax ProjectCompilerUniqueMatrixSyntax

theorem constant_source {m} {Γ : Context m} (truth : Bool) (w b f n q : Fin m)
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f)) (hc : Derives Γ (constant truth w n q)) :
    Derives Γ (ProjectSourceAtomSyntax.atomic w b f n) := by
  cases truth
  · exact .disjL (.disjL (.conjI hctx (.conjL hc)))
  · exact .disjL (.disjR (.conjI hctx (.conjL hc)))

theorem atomic_source {m} {Γ : Context m} (kind : Fin 3) (w b z x y n q f : Fin m)
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f)) (hc : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q)) :
    Derives Γ (ProjectSourceAtomSyntax.atomic w b f n) := by
  have hi := ProjectSourceAtomSyntax.intro_binary kind w b x y n (.conjL hc)
  rcases kind with ⟨i,hiNat⟩
  have h : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact .disjR (.conjI hctx (.disjL hi))
  · exact .disjR (.conjI hctx (.disjR (.disjL hi)))
  · exact .disjR (.conjI hctx (.disjR (.disjR hi)))

theorem single_source {k m} {Γ : Context m} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b f n q x y : Fin m) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hg : Derives Γ (goodQueries P ρ w n f)) (hc : Derives Γ (singleMatrix tag advance P ρ w b n q x y)) :
    Derives Γ (ProjectSourceCodeRecursiveSyntax.singleCase tag advance w b f n) := by
  have hs := ProjectCompilerSourceQueries.check_source advance P ρ w n f x b y hg (.conjL (.conjR hc))
  have hx := ProjectCompilerSourceQueries.check_child_member advance P ρ n x b y (.conjL (.conjR hc))
  exact ProjectSourceCodeRecursiveSyntax.intro_single tag advance w b f x n hctx (.conjI (.conjL hc) (.conjI hx hs))

theorem binary_source {k m} {Γ : Context m} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b f n q x y X Y : Fin m) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hg : Derives Γ (goodQueries P ρ w n f)) (hc : Derives Γ (binaryMatrix kind P ρ w b n q x y X Y)) :
    Derives Γ (ProjectSourceCodeRecursiveSyntax.binaryCase kind w b f n) := by
  have hX := query_source P ρ w n f x b X hg (.conjL (.conjR hc))
  have hY := query_source P ρ w n f y b Y hg (.conjL (.conjR (.conjR hc)))
  have hx := Derives.conjL (Derives.conjL (Derives.conjR hc))
  have hy := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR hc)))
  exact ProjectSourceCodeRecursiveSyntax.intro_binary kind w b f x y n hctx
    (.conjI (.conjL hc) (.conjI hx (.conjI hy (.conjI hX hY))))

theorem mode_source_cases {m} {Γ : Context m} (mode : Mode) (w b z n q f : Fin m) (xs : Fin 4 → Fin m)
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hg : Derives Γ (goodQueries codeMatrix (parameters w) w n f)) (hc : Derives Γ (matrix mode w b z n q xs)) :
    Derives Γ (ProjectSourceCodeRecursiveSyntax.allCases w n b f) := by
  cases mode
  · exact .disjL (constant_source false w b f n q hctx hc)
  · exact .disjL (constant_source true w b f n q hctx hc)
  · exact .disjL (atomic_source 0 w b z (xs 0) (xs 1) n q f hctx hc)
  · exact .disjL (atomic_source 1 w b z (xs 0) (xs 1) n q f hctx hc)
  · exact .disjL (atomic_source 2 w b z (xs 0) (xs 1) n q f hctx hc)
  · exact (.disjR (.disjL (single_source 4 false codeMatrix (parameters w) w b f n q (xs 0) (xs 1) hctx hg hc)))
  · exact (.disjR (.disjR (.disjL (binary_source 0 codeMatrix (parameters w) w b f n q (xs 0) (xs 1) (xs 2) (xs 3) hctx hg hc))))
  · exact (.disjR (.disjR (.disjR (.disjL (binary_source 1 codeMatrix (parameters w) w b f n q (xs 0) (xs 1) (xs 2) (xs 3) hctx hg hc)))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjL (binary_source 2 codeMatrix (parameters w) w b f n q (xs 0) (xs 1) (xs 2) (xs 3) hctx hg hc))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (binary_source 3 codeMatrix (parameters w) w b f n q (xs 0) (xs 1) (xs 2) (xs 3) hctx hg hc)))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (single_source 9 true codeMatrix (parameters w) w b f n q (xs 0) (xs 1) hctx hg hc))))))))
  · exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (single_source 10 true codeMatrix (parameters w) w b f n q (xs 0) (xs 1) hctx hg hc))))))))

end PPAC.Migration.Internal.ProjectCompilerSourceMatrix
