def nextMove(gameState):
    import random
    import itertools
    from collections import Counter

    SUITS = ["H", "D", "C", "S"]
    RANKS = list(range(2, 15))

    # -------------------------------------------------------------
    # Self-contained hand evaluator (mirrors the engine's ranking)
    # -------------------------------------------------------------
    def straight_high(ranks):
        unique = sorted(set(ranks), reverse=True)
        if 14 in unique:
            unique = unique + [1]
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

    def best_hand(hole, board):
        all_cards = list(hole) + list(board)
        best = None
        for combo in itertools.combinations(all_cards, 5):
            score = evaluate_five(combo)
            if best is None or score > best:
                best = score
        return best

    # -------------------------------------------------------------
    # Gather state
    # -------------------------------------------------------------
    hole = gameState.your_hole_cards
    board = gameState.community_cards
    pot = gameState.pot
    to_call = gameState.amount_to_call
    stack = gameState.your_stack
    min_raise_to = gameState.min_raise_to

    active_opponents = [
        p for p in gameState.seat_order
        if p != gameState.your_name and gameState.player_status.get(p) != "folded"
    ]
    num_opp = len(active_opponents)

    if num_opp == 0:
        return ("check",) if to_call == 0 else ("call",)

    # -------------------------------------------------------------
    # Monte Carlo equity estimate: simulate random opponent hands and
    # random remaining board cards, using our own hand evaluator, to
    # get a real win/tie rate rather than a hand-strength lookup table.
    # Works identically on every street, including preflop.
    # -------------------------------------------------------------
    known = set(hole) | set(board)
    deck = [(s, r) for s in SUITS for r in RANKS if (s, r) not in known]
    cards_needed = 5 - len(board)

    trials = max(60, min(300, 4000 // max(1, num_opp)))

    wins = 0.0
    for _ in range(trials):
        pool = deck[:]
        random.shuffle(pool)
        idx = 0
        opp_holes = []
        for _ in range(num_opp):
            opp_holes.append((pool[idx], pool[idx + 1]))
            idx += 2
        sim_board = board + pool[idx:idx + cards_needed]

        my_score = best_hand(hole, sim_board)
        best_score = my_score
        tie_count = 1
        beaten = False
        for oh in opp_holes:
            osc = best_hand(oh, sim_board)
            if osc > best_score:
                beaten = True
                break
            elif osc == best_score:
                tie_count += 1
        if not beaten:
            wins += 1.0 / tie_count

    equity = wins / trials

    # -------------------------------------------------------------
    # Track our own commitment this street so we can compute an
    # accurate all-in raise total (the engine doesn't expose our
    # current street wager directly, only remaining stack).
    # -------------------------------------------------------------
    if not hasattr(nextMove, "_state"):
        nextMove._state = {"hand": None, "street": None, "committed": 0}
    st = nextMove._state
    if st["hand"] != gameState.hand_number or st["street"] != gameState.street:
        st["hand"] = gameState.hand_number
        st["street"] = gameState.street
        st["committed"] = 0

    max_raise_to = st["committed"] + stack  # all-in total for this street

    # Light range-narrowing heuristic: opponents who have bet/raised
    # this street likely hold stronger hands than a uniformly random
    # one, so nudge our equity estimate down per aggressive action seen.
    aggression = sum(1 for (_, a) in gameState.action_history if a[0] in ("bet", "raise"))
    equity_adj = max(0.0, equity - 0.03 * aggression)

    call_needed_equity = to_call / (pot + to_call) if (pot + to_call) > 0 else 0.0

    def do_call():
        st["committed"] += min(to_call, stack)
        return ("call",)

    def do_bet(amount):
        amount = max(1, min(int(amount), stack))
        st["committed"] += amount
        return ("bet", amount)

    def do_raise(total):
        total = max(min_raise_to, min(int(total), max_raise_to))
        st["committed"] = total
        return ("raise", total)

    # -------------------------------------------------------------
    # Decision logic
    # -------------------------------------------------------------
    if to_call == 0:
        if equity_adj > 0.90 and num_opp <= 2:
            return do_bet(stack)  # shove monster hands for max value heads-up/short-handed
        if equity_adj > 0.65:
            bet_frac = 0.5 + 0.5 * min(1.0, (equity_adj - 0.65) / 0.35)
            amount = int(pot * bet_frac) if pot > 0 else max(1, int(stack * 0.2))
            return do_bet(amount)
        if equity_adj > 0.50 and num_opp <= 3:
            amount = int(pot * 0.4) if pot > 0 else max(1, int(stack * 0.1))
            return do_bet(amount)
        return ("check",)
    else:
        if min_raise_to is not None and equity_adj > 0.60 and equity_adj >= call_needed_equity + 0.15:
            if equity_adj > 0.88:
                return do_raise(max_raise_to)  # shove with a near-nut hand
            return do_raise(min_raise_to + int(pot * 0.5))
        if equity_adj >= call_needed_equity:
            return do_call()
        return ("fold",)