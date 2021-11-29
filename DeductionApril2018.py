from Expression import Expression, CompositeExpression, has_head, Equal
from MatchAndSubstitute import Direction, is_equality
from ProofSystem import ExprAndParent, Exprs, BruteForceProofState

from typing import Sequence, List
from typing import cast


def try_rules(
    context: Sequence[Expression],
    goal: Expression,
    general_rules: Sequence[Expression],
    verbosity: int = 0,
) -> List[Expression]:
    """context and context_rules are disjoint, all in context_rules satisfy
    is_rule(), whereas none of those in context do."""

    assert verbosity >= 0

    general = BruteForceProofState(
        [ExprAndParent(r, None) for r in general_rules], [], None, verbosity
    )

    state = BruteForceProofState(
        [ExprAndParent(e, None) for e in context],
        [ExprAndParent(goal, None)],
        general,
        verbosity,
    )

    while True:
        made_progress = False
        # Step 1: work forward from premises to goal.
        found = state.try_all_rules(
            state.context.immediate_non_rules(),
            state.context.immediate_rules(),
            Direction.FORWARD,
        )
        if isinstance(found, bool):
            made_progress = made_progress or found
        else:
            return found

        # Step 2: simplification / transformations from the goal.
        found = state.try_all_rules(
            cast(Exprs, state.goals).immediate_non_rules(),
            state.context.immediate_rules(),
            Direction.BACKWARD,
        )
        if isinstance(found, bool):
            made_progress = made_progress or found
        else:
            return found

        if not made_progress:
            break

    print(
        "Using just the problem specific premises & rules hasn't let us "
        "prove the goal.  Switching to general purpose premises / rules."
    )

    for current_goal in cast(Exprs, state.goals).equalities():
        assert has_head(current_goal.expr, Equal)
        goal_expr = cast(CompositeExpression, current_goal.expr)
        lhs = ExprAndParent(goal_expr[1], None)
        rhs = ExprAndParent(goal_expr[2], current_goal)
        if verbosity > 0:
            print(
                "*** goal: "
                + str(current_goal.expr)
                + ", LHS: "
                + str(lhs.expr)
                + ", target: "
                + str(rhs.expr)
            )
        temp_state = BruteForceProofState([lhs], [rhs], state, verbosity)
        while True:
            print("########  Starting pass!")
            print("************************  context:")
            print("\n".join([str(v) for v in temp_state.context]))
            print("************************  goals:")
            print("\n".join([str(v) for v in temp_state.goals]))

            # We need something smarter than try_all_rules().
            found = temp_state.try_all_rules(
                temp_state.context.all_exprs(),
                temp_state.context.all_rules(),
                Direction.FORWARD,
            )
            if not isinstance(found, bool):
                return found

            if not found:
                break

    print("************************  Final context:")
    print("\n".join([str(v) for v in state.context]))
    print("************************  Final goals:")
    print("\n".join([str(v) for v in state.goals]))

    return []
