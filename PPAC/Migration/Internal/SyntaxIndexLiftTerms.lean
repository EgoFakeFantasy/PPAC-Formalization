import PPAC.Migration.Internal.SyntaxIndexLiftEdges

/-! 量词实际提升保持原项重命名：新bound固定、旧bound同步后继、free图原样保持。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftTerms
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax SyntaxIndexLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem maps_lifted {m} {Γ : Context m} (w r s a b c d u v g : Fin m)
    (hm : Derives Γ (maps w r s a b c d)) (hl : Derives Γ (lifted w r a c u v g)) :
    Derives Γ (maps w g s u b v d) :=
  .conjI (SyntaxIndexLift.target_map w r a c u v g hl) (.conjR hm)

theorem new_bound_fixed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d u v g z n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hl : Derives Γ (lifted w r a c u v g)) (hz : Derives Γ (empty z)) (hn : Derives Γ (code true w z n)) :
    Derives Γ (SyntaxRenameTermSyntax.renamed w g s u b v d n n) := by
  have hmaps := maps_lifted w r s a b c d u v g hm hl
  have hi := SyntaxIndexLiftOrder.zero_member hZ w a u z hw (.conjL (.conjL (.conjL hl))) (.conjL (.conjR hl)) hz
  have he := Derives.impE (.conjR (SyntaxIndexLiftEdges.zero_iff hZ w r a c u v g z z hw hl hz)) hz
  exact SyntaxRenameTermSyntax.intro_renamed true w g s u b v d n n hmaps
    (SyntaxRenameTermSyntax.intro_branch true w g u n n z z hi he hn hn)

theorem old_bound_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r s a b c d u v g i j k l n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d)) (hl : Derives Γ (lifted w r a c u v g))
    (hk : Derives Γ (.mem k a)) (he : Derives Γ (edge r k l))
    (hi : Derives Γ (successor i k)) (hj : Derives Γ (successor j l))
    (hn : Derives Γ (code true w i n)) (hq : Derives Γ (code true w j q)) :
    Derives Γ (SyntaxRenameTermSyntax.renamed w g s u b v d n q) := by
  have hmaps := maps_lifted w r s a b c d u v g hm hl
  have hs := intro_shifted r a i j k l hk he hi hj
  have hsrc := SyntaxIndexLiftPoint.source_member hZ w r a u i j hw (.conjL (.conjL (.conjL hl))) (.conjL (.conjR hl)) (.disjR hs)
  have heg := Derives.impE (.conjR (SyntaxIndexLift.edge_iff hZ w r a c u v g i j hw hl)) (.disjR hs)
  exact SyntaxRenameTermSyntax.intro_renamed true w g s u b v d n q hmaps
    (SyntaxRenameTermSyntax.intro_branch true w g u n q i j hsrc heg hn hq)

theorem free_preserved {m} {Γ : Context m} (w r s a b c d u v g i j n q : Fin m)
    (hm : Derives Γ (maps w r s a b c d)) (hl : Derives Γ (lifted w r a c u v g))
    (hi : Derives Γ (.mem i b)) (he : Derives Γ (edge s i j))
    (hn : Derives Γ (code false w i n)) (hq : Derives Γ (code false w j q)) :
    Derives Γ (SyntaxRenameTermSyntax.renamed w g s u b v d n q) :=
  SyntaxRenameTermSyntax.intro_renamed false w g s u b v d n q (maps_lifted w r s a b c d u v g hm hl)
    (SyntaxRenameTermSyntax.intro_branch false w s b n q i j hi he hn hq)
end PPAC.Migration.Internal.SyntaxIndexLiftTerms
