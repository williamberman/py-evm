import itertools

from eth_typing import Address

from eth.abc import TransactionContextAPI
from eth.validation import (
    validate_canonical_address,
    validate_uint256,
)


class BaseTransactionContext(TransactionContextAPI):
    __slots__ = ['_gas_price', '_origin', '_log_counter']

    def __init__(self, gas_price: int, origin: Address, start=0) -> None:
        validate_uint256(gas_price, title="TransactionContext.gas_price")
        self._gas_price = gas_price
        validate_canonical_address(origin, title="TransactionContext.origin")
        self._origin = origin
        self._log_counter = itertools.count(start)

    def get_next_log_counter(self) -> int:
        return next(self._log_counter)

    @property
    def gas_price(self) -> int:
        return self._gas_price

    @property
    def origin(self) -> Address:
        return self._origin

    def copy(self) -> TransactionContextAPI:
        # You can't get a reference to the current value in an iterator. 
        # So instead we have to consume the current counter and then reset it
        # Kids, don't use itertools.count when an integer will do
        # TODO should change to just using a counter if doesn't break any tests
        cur = next(self._log_counter)
        self._log_counter = itertools.count(cur)
        return BaseTransactionContext(self._gas_price, self._origin, cur)
