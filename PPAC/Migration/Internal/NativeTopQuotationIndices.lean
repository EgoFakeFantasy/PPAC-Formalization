import PPAC.Migration.Internal.ObjectNativeFormulaQuotation

/-! 纯签名有限上下文的确定变量位置模式；不是从内部模型或集合列表抽取值。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationIndices
open PureSyntaxQuotation NativeSubstitutionSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

def entryAt : (scope : Ctx) → Fin scope.length → Variable scope SetSort.set
  | List.nil, j => Fin.elim0 j
  | List.cons SetSort.set tail, j => Fin.cases .here (fun k => .there (entryAt tail k)) j

theorem index_entryAt (scope : Ctx) (j : Fin scope.length) : (entryAt scope j).index = j.val := by
  induction scope with
  | nil => exact Fin.elim0 j
  | cons sort tail ih =>
    cases sort
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact congrArg (· + 1) (ih k)

def sourceIndex {source bound free : Ctx} (σ : Mapping source bound free) (j : Fin (NativeSubstitutionImages.images source σ).length) : Fin source.length :=
  ⟨j.val, by simpa only [NativeSubstitutionImages.images_length] using j.isLt⟩

theorem get_at {source bound free : Ctx} (σ : Mapping source bound free) (j : Fin (NativeSubstitutionImages.images source σ).length) :
    (NativeSubstitutionImages.images source σ).get j = σ (entryAt source (sourceIndex σ j)) := by
  have he : NativeSubstitutionImages.entryIndex σ (entryAt source (sourceIndex σ j)) = j := by
    apply Fin.ext
    exact index_entryAt source (sourceIndex σ j)
  have ho := NativeSubstitutionImages.get_image σ (entryAt source (sourceIndex σ j))
  rw [he] at ho
  exact ho

def instantiateBound {bound free : Ctx} (replacement : Tm bound free) : Mapping (SetSort.set :: bound) bound free :=
  VariableSubstitution.instantiateTop replacement

def identityFree {bound free : Ctx} : Mapping free bound free := fun entry => .fvar entry

def abstractBound {bound free : Ctx} : Mapping bound (SetSort.set :: bound) free := fun entry => .bvar (.there entry)

def abstractFree {bound free : Ctx} : Mapping (SetSort.set :: free) (SetSort.set :: bound) free :=
  fun entry => match entry with | .here => .bvar .here | .there previous => .fvar previous

theorem instantiateBound_eq {bound free : Ctx} (replacement : Tm bound free) :
    @instantiateBound bound free replacement = @VariableSubstitution.instantiateTop ℒ bound free SetSort.set replacement := rfl

theorem identityFree_eq {bound free : Ctx} : @identityFree bound free = @VariableSubstitution.freeId ℒ bound free := rfl

theorem abstractBound_eq {bound free : Ctx} : @abstractBound bound free = @VariableSubstitution.abstractBound ℒ bound free SetSort.set := rfl

theorem abstractFree_eq {bound free : Ctx} : @abstractFree bound free = @VariableSubstitution.abstractFreeTop ℒ bound free SetSort.set := by
  funext sort entry
  cases entry <;> rfl

theorem instantiate_formula {bound free : Ctx} (input : Fm (SetSort.set :: bound) free) (replacement : Tm bound free) :
    input.substituteMapped (instantiateBound replacement) (@identityFree bound free) = input.instantiateTop replacement := rfl

theorem abstract_formula {bound free : Ctx} (input : Fm bound (SetSort.set :: free)) :
    input.substituteMapped (@abstractBound bound free) (@abstractFree bound free) = input.abstractFreeTop := by
  unfold Formula.abstractFreeTop Formula.substitute Substitution.abstractFreeTop
  rw [abstractBound_eq, abstractFree_eq]

end PPAC.Migration.Internal.NativeTopQuotationIndices
