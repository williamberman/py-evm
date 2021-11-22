from eth.abc import MemoryAPI
from eth.exceptions import (
    InvalidJumpDestination,
    InvalidInstruction,
    Halt,
)

from eth.vm.computation import BaseComputation
from eth.vm.memory import Memory
from eth.vm.opcode_values import (
    JUMPDEST,
)

import copy

from eth.vm.stack import Stack

import pdb

def stop(computation: BaseComputation) -> None:
    raise Halt('STOP')


def jump(computation: BaseComputation) -> None:
    jump_dest = computation.stack_pop1_int()

    computation.code.program_counter = jump_dest

    next_opcode = computation.code.peek()

    if next_opcode != JUMPDEST:
        raise InvalidJumpDestination("Invalid Jump Destination")

    if not computation.code.is_valid_opcode(jump_dest):
        raise InvalidInstruction("Jump resulted in invalid instruction")


def jumpi(computation: BaseComputation, jump_dest=None, check_value=None) -> None:
    if jump_dest is None and check_value is None:
        jump_dest, check_value = computation.stack_pop_ints(2)

    if jump_dest is None or check_value is None:
        assert False

    if check_value:
        computation.code.program_counter = jump_dest

        next_opcode = computation.code.peek()

        if next_opcode != JUMPDEST:
            raise InvalidJumpDestination("Invalid Jump Destination")

        if not computation.code.is_valid_opcode(jump_dest):
            raise InvalidInstruction("Jump resulted in invalid instruction")


def sym_jumpi(computation: BaseComputation) -> None:
    print("using symbolic jumpi")
    jump_dest, check_value = computation.stack_pop_ints(2)

    # Let this computation take the jump. 
    # The forked computation can be elected to be taken later by the caller.
    # TODO(will): Check if one of the two paths is not satisfiable.
    # If one of the two is not, then just continue executing on the
    # current path that is.

    if isinstance(check_value, int):
        jumpi(computation, jump_dest=jump_dest, check_value=check_value)
        return

    no_jump_computation = computation.fork()
    no_jump_computation.constraints.append(check_value == 0)

    computation.constraints.append(check_value == 1)
    computation.code.program_counter = jump_dest

    next_opcode = computation.code.peek()

    if next_opcode != JUMPDEST:
        raise InvalidJumpDestination("Invalid Jump Destination")

    if not computation.code.is_valid_opcode(jump_dest):
        raise InvalidInstruction("Jump resulted in invalid instruction")


def jumpdest(computation: BaseComputation) -> None:
    pass


def program_counter(computation: BaseComputation) -> None:
    pc = max(computation.code.program_counter - 1, 0)

    computation.stack_push_int(pc)


def gas(computation: BaseComputation) -> None:
    gas_remaining = computation.get_gas_remaining()

    computation.stack_push_int(gas_remaining)
