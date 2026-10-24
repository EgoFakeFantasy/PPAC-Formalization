import PPAC.Migration.Internal.PacketTraceSyntax

/-! Exact original Packet-table membership and all nonmatching affine-head tags. -/
namespace PPAC.Migration.Internal.PacketAffineDispatchData
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open PacketAffineRuleData (baseRule stepRule relation radix)

def differentOuter {n} (target : Nat) : Expr n → Bool
  | .succ (.pair (.literal tag) _) => tag != target
  | _ => false

def others (wide : Bool) : List Rule :=
  [baseRule (!wide), stepRule (!wide)] ++ ObjectPacket.rules.drop 4

theorem others_classified (wide : Bool) : (others wide).all (fun r => differentOuter (relation wide) r.head) = true := by
  cases wide <;> rfl

theorem others_different (wide : Bool) (rule : Rule) (hr : rule ∈ others wide) :
    differentOuter (relation wide) rule.head = true := List.all_eq_true.mp (others_classified wide) rule hr

theorem outer_shape {n} (target : Nat) (e : Expr n) (he : differentOuter target e = true) :
    ∃ tag payload, tag ≠ target ∧ e = Expr.succ (.pair (.literal tag) payload) := by
  cases e with
  | literal _ | var _ | pair _ _ => cases he
  | succ e =>
    cases e with
    | literal _ | var _ | succ _ => cases he
    | pair a payload =>
      cases a with
      | var _ | succ _ | pair _ _ => cases he
      | literal tag => exact ⟨tag,payload,by simpa only [differentOuter,bne_iff_ne] using he,rfl⟩

theorem base_member (wide : Bool) : baseRule wide ∈ ObjectPacket.rules := by
  cases wide
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem step_member (wide : Bool) : stepRule wide ∈ ObjectPacket.rules := by
  cases wide
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem rule_cases (wide : Bool) (rule : Rule) (hr : rule ∈ ObjectPacket.rules) :
    rule = baseRule wide ∨ rule = stepRule wide ∨ rule ∈ others wide := by
  cases wide
  all_goals
    simp only [ObjectPacket.rules,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (by simp [others, PacketAffineRuleData.baseRule, PacketAffineRuleData.stepRule,
          PacketAffineRuleData.relation, PacketAffineRuleData.radix, ObjectPacket.rules]))


end PPAC.Migration.Internal.PacketAffineDispatchData
