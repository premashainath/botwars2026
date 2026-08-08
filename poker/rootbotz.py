def nextMove(gameState):
    import itertools
    import math
    import random
    import time
    from collections import Counter

    SUITS = ("H", "D", "C", "S")
    RANKS = tuple(range(2, 15))
    FULL_DECK = tuple(
        (s, r)
        for s in SUITS
        for r in RANKS
    )

    STARTING_STACK = 50000

    TIME_BUDGET_SECONDS = 0.75
    MAX_SIMS = 2200
    MAX_RANGE_TRIES = 4

    def _straight_high(ranks):
        unique = sorted(
            set(ranks),
            reverse=True
        )

        if 14 in unique:
            unique.append(1)

        unique = sorted(
            set(unique),
            reverse=True
        )

        for i in range(
            len(unique) - 4
        ):
            window = unique[i:i + 5]

            if (
                window[0]
                - window[4]
                == 4
            ):
                return window[0]

        return None

    def _evaluate_five(cards):
        ranks = sorted(
            (
                c[1]
                for c in cards
            ),
            reverse=True
        )

        suits = [
            c[0]
            for c in cards
        ]

        counts = Counter(ranks)

        by_freq = sorted(
            counts.items(),
            key=lambda x: (
                x[1],
                x[0]
            ),
            reverse=True
        )

        is_flush = (
            len(set(suits))
            == 1
        )

        straight_high = (
            _straight_high(ranks)
        )

        if (
            is_flush
            and straight_high
            is not None
        ):
            return (
                8,
                straight_high
            )

        if by_freq[0][1] == 4:
            quad = by_freq[0][0]

            kicker = max(
                r
                for r in ranks
                if r != quad
            )

            return (
                7,
                quad,
                kicker
            )

        if (
            by_freq[0][1] == 3
            and len(by_freq) > 1
            and by_freq[1][1] >= 2
        ):
            return (
                6,
                by_freq[0][0],
                by_freq[1][0]
            )

        if is_flush:
            return (
                5,
                tuple(ranks)
            )

        if straight_high is not None:
            return (
                4,
                straight_high
            )

        if by_freq[0][1] == 3:
            trips = by_freq[0][0]

            kickers = sorted(
                [
                    r
                    for r in ranks
                    if r != trips
                ],
                reverse=True
            )[:2]

            return (
                3,
                trips,
                tuple(kickers)
            )

        pairs = sorted(
            [
                rank
                for rank, count
                in counts.items()
                if count == 2
            ],
            reverse=True
        )

        if len(pairs) >= 2:
            hi = pairs[0]
            lo = pairs[1]

            kicker = max(
                r
                for r in ranks
                if r not in (
                    hi,
                    lo
                )
            )

            return (
                2,
                hi,
                lo,
                kicker
            )

        if len(pairs) == 1:
            pair = pairs[0]

            kickers = sorted(
                [
                    r
                    for r in ranks
                    if r != pair
                ],
                reverse=True
            )[:3]

            return (
                1,
                pair,
                tuple(kickers)
            )

        return (
            0,
            tuple(ranks)
        )

    def _evaluate_best_hand(
        hole,
        board
    ):
        all_cards = (
            list(hole)
            + list(board)
        )

        if len(all_cards) < 5:
            ranks = sorted(
                [
                    c[1]
                    for c in all_cards
                ],
                reverse=True
            )

            return (
                -1,
                tuple(ranks)
            )

        best = None

        for combo in itertools.combinations(
            all_cards,
            5
        ):
            score = (
                _evaluate_five(combo)
            )

            if (
                best is None
                or score > best
            ):
                best = score

        return best

    def _chen_points(rank):
        return {
            14: 10.0,
            13: 8.0,
            12: 7.0,
            11: 6.0
        }.get(
            rank,
            rank / 2.0
        )

    def _chen_strength_raw(
        card1,
        card2
    ):
        r1 = card1[1]
        r2 = card2[1]

        hi = max(r1, r2)
        lo = min(r1, r2)

        if hi == lo:
            pts = max(
                _chen_points(hi) * 2,
                5.0
            )

        else:
            pts = _chen_points(hi)

            if (
                card1[0]
                == card2[0]
            ):
                pts += 2

            gap = (
                hi - lo - 1
            )

            if gap == 0:
                if hi <= 12:
                    pts += 1

            elif gap == 1:
                pts -= 1

                if hi <= 12:
                    pts += 1

            elif gap == 2:
                pts -= 2

            elif gap == 3:
                pts -= 4

            else:
                pts -= 5

        pts = max(
            pts,
            0.0
        )

        return (
            math.ceil(
                pts * 2
            )
            / 2.0
        )

    def _chen_strength(
        card1,
        card2
    ):
        return min(
            _chen_strength_raw(
                card1,
                card2
            ) / 20.0,
            1.0
        )

    def _build_opponent_profiles(
        your_name,
        hand_history
    ):
        profiles = {}

        if not hand_history:
            return profiles

        try:
            for entry in hand_history:
                showdown = (
                    entry.get(
                        "showdown"
                    )
                    or {}
                )

                for (
                    name,
                    cards
                ) in showdown.items():

                    if (
                        name == your_name
                        or len(cards) != 2
                    ):
                        continue

                    p = profiles.setdefault(
                        name,
                        {
                            "strengths": [],
                            "bets": 0,
                            "acts": 0
                        }
                    )

                    try:
                        p[
                            "strengths"
                        ].append(
                            _chen_strength(
                                cards[0],
                                cards[1]
                            )
                        )

                    except Exception:
                        pass

                actions_by_street = (
                    entry.get(
                        "actions"
                    )
                    or {}
                )

                for street_actions in (
                    actions_by_street.values()
                ):
                    for item in street_actions:

                        if (
                            not isinstance(
                                item,
                                (tuple, list)
                            )
                            or len(item) < 2
                        ):
                            continue

                        name = item[0]
                        action = item[1]

                        if name == your_name:
                            continue

                        p = profiles.setdefault(
                            name,
                            {
                                "strengths": [],
                                "bets": 0,
                                "acts": 0
                            }
                        )

                        p["acts"] += 1

                        if (
                            action
                            and isinstance(
                                action,
                                (tuple, list)
                            )
                            and action[0]
                            in ("bet", "raise")
                        ):
                            p["bets"] += 1

        except Exception:
            return {}

        summary = {}

        for name, p in (
            profiles.items()
        ):
            if p["strengths"]:
                avg_strength = (
                    sum(
                        p["strengths"]
                    )
                    / len(
                        p["strengths"]
                    )
                )
            else:
                avg_strength = None

            if p["acts"]:
                aggression = (
                    p["bets"]
                    / p["acts"]
                )
            else:
                aggression = None

            summary[name] = {
                "avg_showdown_strength":
                    avg_strength,
                "aggression":
                    aggression,
                "hands_seen":
                    len(
                        p["strengths"]
                    )
            }

        return summary

    def _opponent_range_floor(
        name,
        gs,
        profile
    ):
        floor = 0.0

        try:
            action_history = (
                getattr(
                    gs,
                    "action_history",
                    []
                )
                or []
            )

            acted_aggressively = False

            for item in action_history:
                if (
                    not isinstance(
                        item,
                        (tuple, list)
                    )
                    or len(item) < 2
                ):
                    continue

                actor = item[0]
                action = item[1]

                if (
                    actor == name
                    and action
                    and isinstance(
                        action,
                        (tuple, list)
                    )
                    and action[0]
                    in ("bet", "raise")
                ):
                    acted_aggressively = True
                    break

            if acted_aggressively:
                floor = max(
                    floor,
                    0.50
                )

            stacks = getattr(
                gs,
                "player_stacks",
                {}
            )

            stack_now = stacks.get(
                name,
                STARTING_STACK
            )

            committed_frac = (
                1.0
                - (
                    stack_now
                    / STARTING_STACK
                )
            )

            if committed_frac > 0.25:
                floor = max(
                    floor,
                    0.40
                )

            if committed_frac > 0.50:
                floor = max(
                    floor,
                    0.60
                )

            if (
                floor > 0
                and profile
            ):
                hist = profile.get(
                    "avg_showdown_strength"
                )

                seen = profile.get(
                    "hands_seen",
                    0
                )

                if (
                    hist is not None
                    and seen >= 3
                ):
                    floor = max(
                        floor,
                        min(
                            hist,
                            0.85
                        )
                    )

        except Exception:
            return 0.0

        return min(
            floor,
            0.85
        )

    def _sample_hands_for_sim(
        remaining,
        n_opponents,
        missing_board,
        floors
    ):
        pool = list(remaining)

        opp_hands = []

        for i in range(
            n_opponents
        ):
            if len(pool) < 2:
                return (
                    None,
                    None
                )

            floor = (
                floors[i]
                if i < len(floors)
                else 0.0
            )

            if floor > 0:
                best = None
                best_strength = -1.0
                chosen = None

                for _ in range(
                    MAX_RANGE_TRIES
                ):
                    c1, c2 = (
                        random.sample(
                            pool,
                            2
                        )
                    )

                    strength = (
                        _chen_strength(
                            c1,
                            c2
                        )
                    )

                    if strength >= floor:
                        chosen = (
                            c1,
                            c2
                        )
                        break

                    if (
                        strength
                        > best_strength
                    ):
                        best_strength = (
                            strength
                        )

                        best = (
                            c1,
                            c2
                        )

                if chosen is None:
                    chosen = best

            else:
                chosen = tuple(
                    random.sample(
                        pool,
                        2
                    )
                )

            if chosen is None:
                return (
                    None,
                    None
                )

            pool.remove(
                chosen[0]
            )

            pool.remove(
                chosen[1]
            )

            opp_hands.append(
                [
                    chosen[0],
                    chosen[1]
                ]
            )

        if (
            missing_board
            > len(pool)
        ):
            return (
                None,
                None
            )

        if missing_board:
            extra_board = (
                random.sample(
                    pool,
                    missing_board
                )
            )
        else:
            extra_board = []

        return (
            opp_hands,
            extra_board
        )

    def _estimate_equity(
        hole,
        board,
        opponent_names,
        gs,
        profiles
    ):
        known = (
            set(hole)
            | set(board)
        )

        remaining = [
            c
            for c in FULL_DECK
            if c not in known
        ]

        missing_board = (
            5 - len(board)
        )

        n_opponents = len(
            opponent_names
        )

        if n_opponents <= 0:
            return 1.0

        if (
            n_opponents * 2
            + missing_board
            > len(remaining)
        ):
            return 0.5

        floors = []

        for name in opponent_names:
            try:
                floors.append(
                    _opponent_range_floor(
                        name,
                        gs,
                        profiles.get(name)
                    )
                )
            except Exception:
                floors.append(
                    0.0
                )

        wins = 0.0
        sims = 0

        start = (
            time.perf_counter()
        )

        while (
            sims < MAX_SIMS
            and (
                time.perf_counter()
                - start
            )
            < TIME_BUDGET_SECONDS
        ):
            (
                opp_hands,
                extra_board
            ) = _sample_hands_for_sim(
                remaining,
                n_opponents,
                missing_board,
                floors
            )

            if opp_hands is None:
                break

            full_board = (
                list(board)
                + list(
                    extra_board
                )
            )

            my_score = (
                _evaluate_best_hand(
                    hole,
                    full_board
                )
            )

            opp_scores = [
                _evaluate_best_hand(
                    h,
                    full_board
                )
                for h
                in opp_hands
            ]

            best_opp = max(
                opp_scores
            )

            if my_score > best_opp:
                wins += 1.0

            elif my_score == best_opp:
                tied_players = (
                    1
                    + sum(
                        1
                        for score
                        in opp_scores
                        if score
                        == best_opp
                    )
                )

                wins += (
                    1.0
                    / tied_players
                )

            sims += 1

        if sims == 0:
            return 0.5

        return wins / sims

    if not hasattr(
        nextMove,
        "_track"
    ):
        nextMove._track = {}

    def _street_start_stack(gs):
        track = (
            nextMove._track
        )

        hand_number = getattr(
            gs,
            "hand_number",
            0
        )

        street = getattr(
            gs,
            "street",
            "unknown"
        )

        key = (
            hand_number,
            street
        )

        if key not in track:
            track.clear()

            track[key] = getattr(
                gs,
                "your_stack",
                STARTING_STACK
            )

        return track[key]

    def _field_adjustment(
        opponent_names,
        profiles
    ):
        strengths = []

        for name in opponent_names:
            prof = profiles.get(
                name
            )

            if not prof:
                continue

            strength = prof.get(
                "avg_showdown_strength"
            )

            seen = prof.get(
                "hands_seen",
                0
            )

            if (
                strength is not None
                and seen >= 3
            ):
                strengths.append(
                    strength
                )

        if not strengths:
            return 0.0

        avg = (
            sum(strengths)
            / len(strengths)
        )

        return max(
            -0.05,
            min(
                0.05,
                (avg - 0.45)
                * 0.4
            )
        )

    def _decide(
        gs,
        equity,
        opponent_names,
        profiles
    ):
        pot = max(
            0,
            getattr(
                gs,
                "pot",
                0
            )
        )

        call = max(
            0,
            getattr(
                gs,
                "amount_to_call",
                0
            )
        )

        stack = max(
            0,
            getattr(
                gs,
                "your_stack",
                0
            )
        )

        n_opponents = len(
            opponent_names
        )

        jitter = random.uniform(
            -0.015,
            0.015
        )

        field_adj = (
            _field_adjustment(
                opponent_names,
                profiles
            )
        )

        if call == 0:
            threshold = min(
                0.48
                + 0.045
                * max(
                    0,
                    n_opponents - 1
                )
                + jitter
                + field_adj,
                0.82
            )

            if equity < threshold:
                return (
                    "check",
                )

            edge = (
                equity
                - threshold
            )

            if pot > 0:
                fraction = min(
                    0.35
                    + edge * 2.3,
                    1.35
                )

                amount = int(
                    pot
                    * fraction
                )

            else:
                fraction = min(
                    0.025
                    + edge * 0.55,
                    0.40
                )

                amount = int(
                    stack
                    * fraction
                )

            amount = max(
                1,
                min(
                    amount,
                    stack
                )
            )

            return (
                "bet",
                amount
            )

        denominator = (
            pot + call
        )

        if denominator > 0:
            required = (
                call
                / denominator
            )
        else:
            required = 1.0

        margin = (
            equity
            - required
            - field_adj
        )

        # Controlled bluff-catching:
        # don't fold immediately when pot odds are
        # only slightly unfavorable.
        if margin < -0.035:
            return (
                "fold",
            )

        min_raise_to = getattr(
            gs,
            "min_raise_to",
            None
        )

        if (
            margin < 0.10
            or min_raise_to is None
        ):
            return (
                "call",
            )

        all_in_total = (
            _street_start_stack(gs)
        )

        edge = max(
            0.0,
            margin
        )

        target_total = int(
            min_raise_to
            + pot
            * min(
                0.40
                + edge * 2.0,
                1.55
            )
        )

        # Very strong ranges can apply maximum pressure.
        if margin > 0.34:
            target_total = (
                all_in_total
            )

        target_total = max(
            min_raise_to,
            min(
                target_total,
                all_in_total
            )
        )

        return (
            "raise",
            target_total
        )

    def _fallback(gs):
        try:
            amount_to_call = max(
                0,
                getattr(
                    gs,
                    "amount_to_call",
                    0
                )
            )

            stack = max(
                1,
                getattr(
                    gs,
                    "your_stack",
                    1
                )
            )

            if amount_to_call == 0:
                return (
                    "check",
                )

            # Only make emergency calls when tiny
            # relative to remaining stack.
            if (
                amount_to_call
                <= stack * 0.04
            ):
                return (
                    "call",
                )

            return (
                "fold",
            )

        except Exception:
            return (
                "fold",
            )

    try:
        player_status = (
            getattr(
                gameState,
                "player_status",
                {}
            )
            or {}
        )

        opponent_names = [
            name
            for name, status
            in player_status.items()
            if (
                name
                != gameState.your_name
                and status
                != "folded"
            )
        ]

        try:
            profiles = (
                _build_opponent_profiles(
                    gameState.your_name,
                    getattr(
                        gameState,
                        "hand_history",
                        []
                    )
                )
            )
        except Exception:
            profiles = {}

        hole = list(
            getattr(
                gameState,
                "your_hole_cards",
                []
            )
        )

        board = list(
            getattr(
                gameState,
                "community_cards",
                []
            )
        )

        equity = (
            _estimate_equity(
                hole,
                board,
                opponent_names,
                gameState,
                profiles
            )
        )

        return _decide(
            gameState,
            equity,
            opponent_names,
            profiles
        )

    except Exception:
        return _fallback(
            gameState
        )