import PPAC.Migration.Internal.ObjectTermLiftQuotation

/-! 原纯签名变量替换的确定有限项像列表；位置与原变量index相同，量词下两表提升严格交换。 -/
namespace PPAC.Migration.Internal.NativeSubstitutionImages
open PureSyntaxQuotation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

def images {bound free : Ctx} : (source : Ctx) → VariableSubstitution ℒ source bound free → List (Tm bound free)
  | List.nil, _ => List.nil
  | List.cons SetSort.set tail, σ => σ .here :: images tail (fun entry => σ (.there entry))

theorem images_length {source bound free : Ctx} (σ : VariableSubstitution ℒ source bound free) :
    (images source σ).length = source.length := by
  induction source with
  | nil => rfl
  | cons sort tail ih =>
    cases sort
    simp only [images, List.length_cons, ih]

def entryIndex {source bound free : Ctx} (σ : VariableSubstitution ℒ source bound free) (entry : Variable source SetSort.set) :
    Fin (images source σ).length := ⟨entry.index, by simpa only [images_length] using entry.index_lt_length⟩

theorem get_image {source bound free : Ctx} (σ : VariableSubstitution ℒ source bound free) (entry : Variable source SetSort.set) :
    (images source σ).get (entryIndex σ entry) = σ entry := by
  induction source with
  | nil => nomatch entry
  | cons sort tail ih =>
    cases sort
    cases entry with
    | here => rfl
    | there entry => exact ih (fun e => σ (.there e)) entry

theorem images_weaken {source bound free : Ctx} (σ : VariableSubstitution ℒ source bound free) :
    images source (VariableSubstitution.weakenBound SetSort.set σ) = TermQuotationLiftSyntax.shifted (images source σ) := by
  induction source with
  | nil => rfl
  | cons sort tail ih =>
    cases sort
    simp only [images, VariableSubstitution.weakenBound, TermQuotationLiftSyntax.shifted, List.map_cons]
    exact congrArg (List.cons ((σ .here).weakenBound SetSort.set)) (ih (fun entry => σ (.there entry)))

theorem images_lift {source bound free : Ctx} (σ : VariableSubstitution ℒ source bound free) :
    images (SetSort.set :: source) (VariableSubstitution.liftBound SetSort.set σ) = TermQuotationLiftSyntax.newBound (images source σ) := by
  change Term.bvar Variable.here :: images source (VariableSubstitution.weakenBound SetSort.set σ) = _
  rw [images_weaken]
  rfl

end PPAC.Migration.Internal.NativeSubstitutionImages
