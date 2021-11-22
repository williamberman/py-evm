from eth_utils.toolz import (
    curry,
)

from eth import constants

from eth._utils.numeric import (
    unsigned_to_signed,
    signed_to_unsigned,
    ceil8,
)

from eth.vm.computation import BaseComputation

import pdb
import z3
from eth.vm.logic.symbolic import *

def add(computation: BaseComputation) -> None:
    """
    Addition
    """
    left, right = computation.stack_pop_ints(2)

    result = (left + right) & constants.UINT_256_MAX

    computation.stack_push_int(result)


def addmod(computation: BaseComputation) -> None:
    """
    Modulo Addition
    """
    left, right, mod = computation.stack_pop_ints(3)

    if mod == 0:
        result = 0
    else:
        result = (left + right) % mod

    computation.stack_push_int(result)


def sub(computation: BaseComputation) -> None:
    """
    Subtraction
    """
    left, right = computation.stack_pop_ints(2)

    result = (left - right) & constants.UINT_256_MAX

    computation.stack_push_int(result)


def mod(computation: BaseComputation) -> None:
    """
    Modulo
    """
    value, mod = computation.stack_pop_ints(2)

    if mod == 0:
        result = 0
    else:
        result = value % mod

    computation.stack_push_int(result)


def smod(computation: BaseComputation) -> None:
    """
    Signed Modulo
    """
    value, mod = map(
        unsigned_to_signed,
        computation.stack_pop_ints(2),
    )

    pos_or_neg = -1 if value < 0 else 1

    if mod == 0:
        result = 0
    else:
        result = (abs(value) % abs(mod) * pos_or_neg) & constants.UINT_256_MAX

    computation.stack_push_int(signed_to_unsigned(result))


def mul(computation: BaseComputation, left=None, right=None) -> None:
    """
    Multiplication
    """
    if left is None and right is None:
        left, right = computation.stack_pop_ints(2)

    if left is None or right is None:
        assert False

    result = (left * right) & constants.UINT_256_MAX

    computation.stack_push_int(result)

def sym_mul(computation: BaseComputation) -> None:
    """
    Symbolic Multiplication
    """
    left, right = computation.stack_pop_ints(2)

    if isinstance(left, int) and isinstance(right, int):
        mul(computation, left=left, right=right)
        return

    result = (left * right) & constants.UINT_256_MAX

    computation.stack_push_symbolic_int(result)


def mulmod(computation: BaseComputation) -> None:
    """
    Modulo Multiplication
    """
    left, right, mod = computation.stack_pop_ints(3)

    if mod == 0:
        result = 0
    else:
        result = (left * right) % mod
    computation.stack_push_int(result)


def div(computation: BaseComputation, numerator=None, denominator=None) -> None:
    """
    Division
    """
    if numerator is None and denominator is None:
        numerator, denominator = computation.stack_pop_ints(2)

    if numerator is None or denominator is None:
        assert False

    if denominator == 0:
        result = 0
    else:
        result = (numerator // denominator) & constants.UINT_256_MAX

    computation.stack_push_int(result)

def sym_div(computation: BaseComputation) -> None:
    """
    Symbolic Division
    """
    numerator, denominator = computation.stack_pop_ints(2)

    if isinstance(numerator, int) and isinstance(denominator, int):
        div(computation, numerator=numerator, denominator=denominator)
        return

    cond = denominator == 0
    result = z3.BitVec(computation.symgen('div_result'), 256)

    computation.constraints.append(
        z3.Implies(cond, result == 0)
    )

    computation.constraints.append(
        # TODO(will): Probably not exactly correct
        z3.Implies(z3.Not(cond), result == numerator / denominator)
    )

    computation.stack_push_symbolic_int(result)


def sdiv(computation: BaseComputation) -> None:
    """
    Signed Division
    """
    numerator, denominator = map(
        unsigned_to_signed,
        computation.stack_pop_ints(2),
    )

    pos_or_neg = -1 if numerator * denominator < 0 else 1

    if denominator == 0:
        result = 0
    else:
        result = (pos_or_neg * (abs(numerator) // abs(denominator)))

    computation.stack_push_int(signed_to_unsigned(result))


@curry
def exp(computation: BaseComputation, gas_per_byte: int) -> None:
    """
    Exponentiation
    """
    base, exponent = computation.stack_pop_ints(2)

    bit_size = exponent.bit_length()
    byte_size = ceil8(bit_size) // 8

    if exponent == 0:
        result = 1
    elif base == 0:
        result = 0
    else:
        result = pow(base, exponent, constants.UINT_256_CEILING)

    computation.consume_gas(
        gas_per_byte * byte_size,
        reason="EXP: exponent bytes",
    )

    computation.stack_push_int(result)


def signextend(computation: BaseComputation) -> None:
    """
    Signed Extend
    """
    bits, value = computation.stack_pop_ints(2)

    if bits <= 31:
        testbit = bits * 8 + 7
        sign_bit = (1 << testbit)
        if value & sign_bit:
            result = value | (constants.UINT_256_CEILING - sign_bit)
        else:
            result = value & (sign_bit - 1)
    else:
        result = value

    computation.stack_push_int(result)


def shl(computation: BaseComputation) -> None:
    """
    Bitwise left shift
    """
    shift_length, value = computation.stack_pop_ints(2)

    if shift_length >= 256:
        result = 0
    else:
        result = (value << shift_length) & constants.UINT_256_MAX

    computation.stack_push_int(result)


def shr(computation: BaseComputation, shift_length=None, value=None) -> None:
    """
    Bitwise right shift
    """
    if shift_length is None and value is None:
        shift_length, value = computation.stack_pop_ints(2)
    
    if shift_length is None or value is None:
        assert False

    if shift_length >= 256:
        result = 0
    else:
        result = (value >> shift_length) & constants.UINT_256_MAX

    computation.stack_push_int(result)


def sym_shr(computation: BaseComputation) -> None:
    """
    Symbolic Bitwise right shift
    """
    shift_length, value = computation.stack_pop_ints(2)

    # Let's not worry about dealing with symbolic shift lengths for now
    assert isinstance(shift_length, int)

    if isinstance(value, int):
        shr(computation, shift_length=shift_length, value=value)
        return

    if shift_length >= 256:
        result = 0
    else:
        # TODO(will) `& constants.UINT_256_MAX`
        shifted = ssym(z3.LShR(value, shift_length))
        if isinstance(shifted, int):
            # Short circuit. Don't need to add a constraint
            result = shifted
        else:
            result = computation.symgen('shr_result')
            computation.constraints.append(
                result == shifted
            )

    computation.stack_push_symbolic_int(result)


def sar(computation: BaseComputation) -> None:
    """
    Arithmetic bitwise right shift
    """
    shift_length, value = computation.stack_pop_ints(2)
    value = unsigned_to_signed(value)

    if shift_length >= 256:
        result = 0 if value >= 0 else constants.UINT_255_NEGATIVE_ONE
    else:
        result = (value >> shift_length) & constants.UINT_256_MAX

    computation.stack_push_int(result)
