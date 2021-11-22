from eth import constants

from eth._utils.numeric import (
    signed_to_unsigned,
    unsigned_to_signed,
)

from eth.vm.computation import BaseComputation

import z3

import pdb

def lt(computation: BaseComputation, left=None, right=None) -> None:
    """
    Lesser Comparison
    """
    print('using regular less than')

    if left is None and right is None:
        left, right = computation.stack_pop_ints(2)

    if left is None or right is None:
        assert False

    if left < right:
        result = 1
    else:
        result = 0

    computation.stack_push_int(result)

def sym_lt(computation: BaseComputation) -> None:
    """
    Symbolic Lesser Comparison
    """
    # TODO use regular logging
    print('using symbolic less than')

    left, right = computation.stack_pop_ints(2)

    if isinstance(left, int) and isinstance(right, int):
        lt(computation, left=left,right=right)
        return

    cond = left < right
    result = z3.Int(computation.symgen('lt_result'))

    computation.constraints.append(
        z3.Implies(cond, result == 1)
    )
    computation.constraints.append(
        z3.Implies(z3.Not(cond), result == 0)
    )

    computation.stack_push_symbolic_int(result)


def gt(computation: BaseComputation, left=None, right=None) -> None:
    """
    Greater Comparison
    """
    if left is None and right is None:
        left, right = computation.stack_pop_ints(2)

    if left is None or right is None:
        assert False

    if left > right:
        result = 1
    else:
        result = 0

    computation.stack_push_int(result)


def sym_gt(computation: BaseComputation) -> None:
    """
    Symbolic Greater Comparison
    """
    left, right = computation.stack_pop_ints(2)

    if isinstance(left, int) and isinstance(right, int):
        gt(computation, left=left, right=right)
        return

    cond = left > right
    result = z3.Int(computation.symgen('gt_result'))

    computation.constraints.append(
        z3.Implies(cond, result == 1)
    )

    computation.constraints.append(
        z3.Implies(z3.Not(cond), result == 0)
    )

    computation.stack_push_symbolic_int(result)


def slt(computation: BaseComputation) -> None:
    """
    Signed Lesser Comparison
    """
    left, right = map(
        unsigned_to_signed,
        computation.stack_pop_ints(2),
    )

    if left < right:
        result = 1
    else:
        result = 0

    computation.stack_push_int(signed_to_unsigned(result))


def sgt(computation: BaseComputation) -> None:
    """
    Signed Greater Comparison
    """
    left, right = map(
        unsigned_to_signed,
        computation.stack_pop_ints(2),
    )

    if left > right:
        result = 1
    else:
        result = 0

    computation.stack_push_int(signed_to_unsigned(result))


def eq(computation: BaseComputation, left=None, right=None) -> None:
    """
    Equality
    """
    if left is None and right is None:
        left, right = computation.stack_pop_ints(2)

    if left is None or right is None:
        assert False

    if left == right:
        result = 1
    else:
        result = 0

    computation.stack_push_int(result)

def sym_eq(computation: BaseComputation) -> None:
    """
    Symbolic Equality
    """
    left, right = computation.stack_pop_ints(2)

    if computation.code.program_counter == 0x93:
        # NOTE(will) -- This the program counter where we check if
        # the arguments are equal
        # pdb.set_trace()
        pass

    if isinstance(left, int) and isinstance(right, int):
        eq(computation, left=left, right=right)
        return

    cond = left == right
    result = z3.Int(computation.symgen('eq_result'))

    computation.constraints.append(
        z3.Implies(cond, result == 1)
    )

    computation.constraints.append(
        z3.Implies(z3.Not(cond), result == 0)
    )

    computation.stack_push_symbolic_int(result)


def iszero(computation: BaseComputation, value=None) -> None:
    """
    Not
    """
    if value is None:
        value = computation.stack_pop1_int()

    if value == 0:
        result = 1
    else:
        result = 0

    computation.stack_push_int(result)

def sym_iszero(computation: BaseComputation) -> None:
    """
    Symbolic Not
    """
    value = computation.stack_pop1_symbolic_int()

    if isinstance(value, int):
        iszero(computation, value=value)
        return

    cond = value == 0
    result = z3.Int(computation.symgen('iszero_result'))

    computation.constraints.append(
        z3.Implies(cond, result == 1)
    )

    computation.constraints.append(
        z3.Implies(z3.Not(cond), result == 0)
    )

    computation.stack_push_symbolic_int(result)


def and_op(computation: BaseComputation, left=None, right=None) -> None:
    """
    Bitwise And
    """
    if left is None and right is None:
        left, right = computation.stack_pop_ints(2)

    if left is None or right is None:
        assert False

    result = left & right

    computation.stack_push_int(result)

def sym_and_op(computation: BaseComputation) -> None:
    """
    Symbolic Bitwise And
    """
    left, right = computation.stack_pop_ints(2)

    if isinstance(left, int) and isinstance(right, int):
        and_op(computation, left=left, right=right)
        return

    left = cast_to_bitwise_arg(left)
    right = cast_to_bitwise_arg(right)
    result = z3.BitVec('and_result', 256)

    computation.constraints.append(
        result == left & right
    )

    computation.stack_push_symbolic_int(z3.BV2Int(result))

def cast_to_bitwise_arg(x):
    if isinstance(x, int):
        return x
    
    if x.sort().name() == 'Int':
        return z3.Int2BV(x, 256)

    assert False


def or_op(computation: BaseComputation) -> None:
    """
    Bitwise Or
    """
    left, right = computation.stack_pop_ints(2)

    result = left | right

    computation.stack_push_int(result)


def xor(computation: BaseComputation) -> None:
    """
    Bitwise XOr
    """
    left, right = computation.stack_pop_ints(2)

    result = left ^ right

    computation.stack_push_int(result)


def not_op(computation: BaseComputation) -> None:
    """
    Not
    """
    value = computation.stack_pop1_int()

    result = constants.UINT_256_MAX - value

    computation.stack_push_int(result)


def byte_op(computation: BaseComputation) -> None:
    """
    Bitwise And
    """
    position, value = computation.stack_pop_ints(2)

    if position >= 32:
        result = 0
    else:
        result = (value // pow(256, 31 - position)) % 256

    computation.stack_push_int(result)
