def nextMove(gameState):

    import itertools
    import math
    import random
    import time
    from collections import Counter

    SUITS = ["H", "D", "C", "S"]
    RANKS = list(range(2, 15))
    FULL_DECK = [(s, r) for s in SUITS for r in RANKS]
    STARTING_STACK = 50_000

    TIME_BUDGET_SECONDS = 0.85
    MAX_SIMS = 3000
    MAX_RANGE_TRIES = 4  # rejection-sampling attempts per opponent per sim

    # -----------------------------------------------------------------
    # Hand evaluator (mirrors the engine's evaluate_best_hand exactly).
    # -----------------------------------------------------------------
    def straight_high(ranks):
        unique = sorted(set(ranks), reverse=True)
        if 14 in unique:
            unique.append(1)
        unique = sorted(set(unique), reverse=True)
        for i in range(len(unique) - 4):
            window = unique[i:i + 5]
            if window[0] - window[4] == 4:
                return window[0]
        return None

    def evaluate_five(cards):
        ranks = sorted((c[1] for c in cards), reverse=True)
        suits = [c[0] for c in cards]
        counts = Counter(ranks)
        by_freq = sorted(counts.items(), key=lambda x: (x[1], x[0]), reverse=True)
        is_flush = len(set(suits)) == 1
        s_high = straight_high(ranks)

        if is_flush and s_high:
            return (8, s_high)
        if by_freq[0][1] == 4:
            return (6, by_freq[0][0], by_freq[1][0])
        if by_freq[0][1] == 3 and by_freq[1][1] == 2:
            return (5, by_freq[0][0], by_freq[1][0])
        if is_flush:
            return (4, *ranks)
        if s_high:
            return (3, s_high)
        if by_freq[0][1] == 3:
            trips = by_freq[0][0]
            kickers = [r for r in ranks if r != trips]
            return (2, trips, *kickers)
        if by_freq[0][1] == 2 and by_freq[1][1] == 2:
            hi, lo = max(by_freq[0][0], by_freq[1][0]), min(by_freq[0][0], by_freq[1][0])
            kicker = [r for r in ranks if r not in (hi, lo)][0]
            return (1, hi, lo, kicker)
        if by_freq[0][1] == 2:
            pair = by_freq[0][0]
            kickers = [r for r in ranks if r != pair]
            return (0, pair, *kickers)
        return (-1, *ranks)

    def evaluate_best_hand(hole, board):
        all_cards = list(hole) + list(board)
        best = None
        for combo in itertools.combinations(all_cards, 5):
            score = evaluate_five(combo)
            if best is None or score > best:
                best = score
        return best

    # -----------------------------------------------------------------
    # Chen-formula-style starting-hand strength (0..1), used for range
    # narrowing and for scoring historical showdown hands.
    # -----------------------------------------------------------------
    def chen_points(rank):
        return {14: 10.0, 13: 8.0, 12: 7.0, 11: 6.0}.get(rank, rank / 2.0)

    def chen_strength_raw(card1, card2):
        r1, r2 = card1[1], card2[1]
        hi, lo = max(r1, r2), min(r1, r2)
        if hi == lo:
            pts = max(chen_points(hi) * 2, 5.0)
        else:
            pts = chen_points(hi)
            if card1[0] == card2[0]:
                pts += 2
            gap = hi - lo - 1
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
        pts = max(pts, 0.0)
        return math.ceil(pts * 2) / 2.0

    def chen_strength(card1, card2):
        return min(chen_strength_raw(card1, card2) / 20.0, 1.0)

    # -----------------------------------------------------------------
    # Opponent profiling from hand_history (best-effort; failures
    # degrade to "no data" rather than raising).
    # -----------------------------------------------------------------
    def build_opponent_profiles(your_name, hand_history):
        profiles = {}
        if not hand_history:
            return profiles
        try:
            for entry in hand_history:
                showdown = entry.get("showdown") or {}
                for name, cards in showdown.items():
                    if name == your_name or len(cards) != 2:
                        continue
                    p = profiles.setdefault(name, {"strengths": [], "bets": 0, "acts": 0})
                    try:
                        p["strengths"].append(chen_strength(cards[0], cards[1]))
                    except Exception:
                        pass

                actions_by_street = entry.get("actions") or {}
                for street_actions in actions_by_street.values():
                    for name, action in street_actions:
                        if name == your_name:
                            continue
                        p = profiles.setdefault(name, {"strengths": [], "bets": 0, "acts": 0})
                        p["acts"] += 1
                        if action and action[0] in ("bet", "raise"):
                            p["bets"] += 1
        except Exception:
            return {}

        summary = {}
        for name, p in profiles.items():
            avg_strength = sum(p["strengths"]) / len(p["strengths"]) if p["strengths"] else None
            aggression = p["bets"] / p["acts"] if p["acts"] else None
            summary[name] = {
                "avg_showdown_strength": avg_strength,
                "aggression": aggression,
                "hands_seen": len(p["strengths"]),
            }
        return summary

    def opponent_range_floor(name, gs, profile):
        floor = 0.0
        try:
            acted_aggressively = any(
                a_name == name and a[0] in ("bet", "raise")
                for a_name, a in gs.action_history
            )
            if acted_aggressively:
                floor = max(floor, 0.50)

            stack_now = gs.player_stacks.get(name, STARTING_STACK)
            committed_frac = 1.0 - (stack_now / STARTING_STACK)
            if committed_frac > 0.25:
                floor = max(floor, 0.40)
            if committed_frac > 0.50:
                floor = max(floor, 0.60)

            if floor > 0 and profile:
                hist = profile.get("avg_showdown_strength")
                seen = profile.get("hands_seen", 0)
                if hist is not None and seen >= 3:
                    floor = max(floor, min(hist, 0.85))
        except Exception:
            return 0.0
        return min(floor, 0.85)

    # -----------------------------------------------------------------
    # Equity estimation
    # -----------------------------------------------------------------
    def sample_hands_for_sim(remaining, n_opponents, missing_board, floors):
        pool = list(remaining)
        opp_hands = []
        for i in range(n_opponents):
            floor = floors[i] if i < len(floors) else 0.0
            if len(pool) < 2:
                return None, None
            if floor > 0:
                # Best-of-N rejection sampling: a tight floor can match
                # only a couple percent of hands, so discarding failed
                # tries and falling back to a fully random hand would
                # undo most of the narrowing. Keep the strongest
                # candidate seen even when nothing clears the floor.
                best = None
                best_strength = -1.0
                chosen = None
                for _ in range(MAX_RANGE_TRIES):
                    c1, c2 = random.sample(pool, 2)
                    s = chen_strength(c1, c2)
                    if s >= floor:
                        chosen = (c1, c2)
                        break
                    if s > best_strength:
                        best_strength = s
                        best = (c1, c2)
                if chosen is None:
                    chosen = best
            else:
                chosen = tuple(random.sample(pool, 2))
            pool.remove(chosen[0])
            pool.remove(chosen[1])
            opp_hands.append(list(chosen))

        if missing_board > len(pool):
            return None, None
        extra_board = random.sample(pool, missing_board) if missing_board else []
        return opp_hands, extra_board

    def estimate_equity(hole, board, opponent_names, gs, profiles):
        known = set(hole) | set(board)
        remaining = [c for c in FULL_DECK if c not in known]
        missing_board = 5 - len(board)
        n_opponents = len(opponent_names)

        if n_opponents <= 0 or (n_opponents * 2 + missing_board) > len(remaining):
            return 0.5

        floors = []
        for name in opponent_names:
            try:
                floors.append(opponent_range_floor(name, gs, profiles.get(name)))
            except Exception:
                floors.append(0.0)

        wins = 0.0
        sims = 0
        start = time.time()

        while sims < MAX_SIMS and (time.time() - start) < TIME_BUDGET_SECONDS:
            opp_hands, extra_board = sample_hands_for_sim(remaining, n_opponents, missing_board, floors)
            if opp_hands is None:
                break
            full_board = board + extra_board

            my_score = evaluate_best_hand(hole, full_board)
            opp_scores = [evaluate_best_hand(h, full_board) for h in opp_hands]
            best_opp = max(opp_scores)

            if my_score > best_opp:
                wins += 1.0
            elif my_score == best_opp:
                tied = 1 + sum(1 for s in opp_scores if s == best_opp)
                wins += 1.0 / tied

            sims += 1

        if sims == 0:
            return 0.5
        return wins / sims

    # -----------------------------------------------------------------
    # Street-commitment tracking (persistent on this function object)
    # -----------------------------------------------------------------
    def street_start_stack(gs):
        track = nextMove.__dict__.setdefault("_track", {})
        key = (gs.hand_number, gs.street)
        if key not in track:
            track.clear()
            track[key] = gs.your_stack
        return track[key]

    # -----------------------------------------------------------------
    # Decision logic
    # -----------------------------------------------------------------
    def field_looseness_adjustment(opponent_names, profiles):
        strengths = []
        for name in opponent_names:
            prof = profiles.get(name)
            if prof and prof.get("avg_showdown_strength") is not None and prof.get("hands_seen", 0) >= 3:
                strengths.append(prof["avg_showdown_strength"])
        if not strengths:
            return 0.0
        avg = sum(strengths) / len(strengths)
        return max(-0.05, min(0.05, (avg - 0.45) * 0.4))

    def decide(gs, equity, opponent_names, profiles):
        pot = gs.pot
        call = gs.amount_to_call
        stack = gs.your_stack
        n_opponents = len(opponent_names)

        jitter = random.uniform(-0.02, 0.02)
        field_adj = field_looseness_adjustment(opponent_names, profiles)

        if call == 0:
            threshold = min(0.50 + 0.05 * (n_opponents - 1) + jitter + field_adj, 0.85)
            if equity < threshold:
                return ("check",)

            edge = equity - threshold
            if pot > 0:
                frac = min(0.35 + edge * 2.2, 1.5)
                amount = int(pot * frac)
            else:
                amount = int(stack * min(0.03 + edge * 0.6, 0.5))
            amount = max(1, min(amount, stack))
            return ("bet", amount)

        required = call / (pot + call) if (pot + call) > 0 else 1.0
        margin = (equity - required) - field_adj

        if margin < -0.02:
            return ("fold",)

        if margin < 0.08 or gs.min_raise_to is None:
            return ("call",)

        all_in_total = street_start_stack(gs)
        min_to = gs.min_raise_to
        frac = min(0.45 + margin * 2.0, 1.6)
        target_total = int(min_to + pot * frac)

        if margin > 0.35:
            target_total = all_in_total
        target_total = max(min_to, min(target_total, all_in_total))

        return ("raise", target_total)

    # -----------------------------------------------------------------
    # Entry logic
    # -----------------------------------------------------------------
    try:
        opponent_names = [
            name
            for name, status in gameState.player_status.items()
            if name != gameState.your_name and status != "folded"
        ]

        try:
            profiles = build_opponent_profiles(gameState.your_name, gameState.hand_history)
        except Exception:
            profiles = {}

        equity = estimate_equity(
            gameState.your_hole_cards,
            gameState.community_cards,
            opponent_names,
            gameState,
            profiles,
        )
        return decide(gameState, equity, opponent_names, profiles)

    except Exception:
        try:
            if gameState.amount_to_call == 0:
                return ("check",)
            if gameState.amount_to_call <= gameState.your_stack * 0.05:
                return ("call",)
            return ("fold",)
        except Exception:
            return ("fold",)