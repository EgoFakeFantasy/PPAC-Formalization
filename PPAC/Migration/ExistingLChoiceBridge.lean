/- Bridge the donor Choice public interface to the ALREADY accepted exact
selector/ordinal-enumeration proofs. No new choice or enumeration backend. -/
import PPAC.Migration.ExistingOrdinalEnumeration
namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} (h : M.Models ZFC)
include h
theorem models_zf_l : M.Models ZF := PPAC.Migration.ExistingSmallUnion.models_zf_l h
theorem choice_set_l (A : M.Domain)
    (hn : ∀ a, M.mem a A → ∃ x, M.mem x a)
    (hd : ∀ a, M.mem a A → ∀ b, M.mem b A → a ≠ b → ¬ ∃ x, M.mem x a ∧ M.mem x b) :
    ∃ C, ∀ a, M.mem a A → ∃ x, (M.mem x C ∧ M.mem x a) ∧
      ∀ y, (M.mem y C ∧ M.mem y a) → y = x :=
  PPAC.Migration.ExistingSmallUnion.choice_set_l h A hn hd
theorem selector_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S : M.Domain) :
    ∃ C, ∀ T, M.MemberSubset T S → (∃ x, M.mem x T) →
      ∃ x, M.mem x T ∧ M.PairMember I T x C ∧
        ∀ y, M.mem y T → M.PairMember I T y C → y = x :=
  PPAC.Migration.ExistingSmallUnion.selector_l h I S
theorem ordinal_enum_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (S : M.Domain) :
    ∃ κ F, M.IsOrdinal κ ∧ M.IsSetFunctionFromTo I F κ S ∧ M.IsSetSurjectiveOnto I F κ S :=
  PPAC.Migration.ExistingOrdinalEnumeration.ordinal_enum_l h I S
end YesMetaZFC.SetTheory.ZFC
