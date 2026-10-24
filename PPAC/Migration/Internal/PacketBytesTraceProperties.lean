import PPAC.Migration.Internal.PacketBytesRowMap
import PPAC.Migration.Internal.StructuralListLengthConstruct

/-! Original list validity, length, natural values and the exact zero-length fold follow from real trace witnesses. -/
namespace PPAC.Migration.Internal.PacketBytesTraceProperties
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketBytesTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem list_trace {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (StructuralListTraceSyntax.trace w z e l d f n) := .conjL hf

theorem value_sequence {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (SequenceSyntax.sequence g d w) := .conjL (.conjR hf)

theorem seed_edge {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (edge g z t) := .conjL (.conjR (.conjR hf))

theorem last_edge {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (edge g l a) := .conjL (.conjR (.conjR (.conjR hf)))

theorem byte_links {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (PacketBytesRowSyntax.links w C l f g) := .conjR (.conjR (.conjR (.conjR hf)))

theorem tail_natural {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) : Derives Γ (.mem t w) :=
  .impE (SequenceSyntax.bounded_at g w z t (.conjR (value_sequence _ _ _ _ _ _ _ _ _ _ _ hf))) (seed_edge _ _ _ _ _ _ _ _ _ _ _ hf)

theorem output_natural {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) : Derives Γ (.mem a w) :=
  .impE (SequenceSyntax.bounded_at g w l a (.conjR (value_sequence _ _ _ _ _ _ _ _ _ _ _ hf))) (last_edge _ _ _ _ _ _ _ _ _ _ _ hf)

theorem length {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (StructuralListLengthSyntax.hasLength w n l) := StructuralListLengthSyntax.intro_length _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ _ hf)

theorem valid {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (StructuralListTraceSyntax.valid w n) := StructuralListTraceSyntax.intro_valid _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ _ hf)

end PPAC.Migration.Internal.PacketBytesTraceProperties
