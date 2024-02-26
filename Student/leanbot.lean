inductive State
| s0
| s120
| s240

inductive Rotation
| r0
| r120
| r240

def act : Rotation → State → State :=

def add_rotation : Rotation → Rotation → Rotation
| r0, r => r
| r, r0 => r
| r120, r120 => r240
| r120, r240 => r0
| r240, r120 => r0
| r240, r240 => r120

def sub_state : State → State → Rotation
-- what do u add to the second arg to get to the first arg
| s0, s0 => r0
| s0, s120 => r240
| s0, s240 => r120
| s120, s0 => r120
| s120, s120 => r0
| s120, s240 => r240
| s240, s0 => r240
| s240, s120 => r120
| s240, s240 => r0

instance : Add Rotation := ⟨ add_rotation ⟩
