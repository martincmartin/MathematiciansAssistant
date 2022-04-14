from typing import Sequence
from Expression import Expression


def try_rules(
    context: Sequence[Expression],
    goal: Expression,
    general_rules: Sequence[Expression],
    verbosity: int = 0,
) -> Sequence[Expression]:

    assert verbosity >= 0
