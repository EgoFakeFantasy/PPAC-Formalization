import PPAC.Migration.Internal.PacketAffineRecursive
import YesMetaZFC.Automation.ObjectPacketGraph

/-! Exact finite metadata of the pinned original Packet arithmetic rules; no host evaluator is used. -/
namespace PPAC.Migration.Internal.PacketAffineRuleData
open YesMetaZFC.Automation
open ObjectHorn

def radix (wide : Bool) : Nat := if wide then 256 else 128

def relation (wide : Bool) : Nat := if wide then 1 else 0

def baseRule (wide : Bool) : Rule := ObjectPacket.affineBase (relation wide) (radix wide)

def stepRule (wide : Bool) : Rule := ObjectPacket.affineStep (relation wide) (radix wide)

theorem actual_rules (wide : Bool) : rulesFor ObjectPacket.rules (relation wide) = [baseRule wide,stepRule wide] := by
  cases wide <;> rfl

theorem base_arity (wide : Bool) : (baseRule wide).arity = 1 := rfl

theorem base_head (wide : Bool) : (baseRule wide).head = ObjectPacket.node (n := 1) (relation wide) [.var 0,.literal 0,.var 0] := rfl

theorem base_guards (wide : Bool) : (baseRule wide).guards = [(Expr.var (0 : Fin 1),.literal (radix wide))] := rfl

theorem base_premises (wide : Bool) : (baseRule wide).premises = [] := rfl

theorem step_arity (wide : Bool) : (stepRule wide).arity = 3 := rfl

theorem step_head (wide : Bool) : (stepRule wide).head =
    ObjectPacket.node (n := 3) (relation wide) [.var 0,.succ (.var 1),ObjectPacket.Expr.addConst (radix wide) (.var 2)] := rfl

theorem step_guards (wide : Bool) : (stepRule wide).guards = [] := rfl

theorem step_premises (wide : Bool) : (stepRule wide).premises = [ObjectPacket.node (n := 3) (relation wide) [.var 0,.var 1,.var 2]] := rfl

end PPAC.Migration.Internal.PacketAffineRuleData
