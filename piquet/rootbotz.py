def nextMove(gameState):
    import math
    import random
    from itertools import combinations

    SUITS = ("H", "D", "C", "S")
    RANKS = tuple(range(7, 15))
    FULL_DECK = tuple((s, r) for s in SUITS for r in RANKS)

    # ------------------------------------------------------------------
    # Hand-evaluation helpers
    # ------------------------------------------------------------------
    def _point_pip(card):
        r = card[1]
        if r == 14:
            return 11
        if r >= 10:
            return 10
        return r

    def _best_point(hand):
        best = (0, 0, None)
        for s in SUITS:
            cards = [c for c in hand if c[0] == s]
            if not cards:
                continue
            cand = (len(cards), sum(_point_pip(c) for c in cards), s)
            if cand[:2] > best[:2]:
                best = cand
        return best

    def _all_sequences(hand):
        out = []
        for s in SUITS:
            ranks = sorted(c[1] for c in hand if c[0] == s)
            if not ranks:
                continue
            start = 0
            for i in range(1, len(ranks) + 1):
                if i == len(ranks) or ranks[i] != ranks[i - 1] + 1:
                    length = i - start
                    if length >= 3:
                        out.append((length, ranks[i - 1], s))
                    start = i
        return out

    def _best_sequence(hand):
        seqs = _all_sequences(hand)
        return max(seqs, key=lambda x: (x[0], x[1])) if seqs else None

    def _best_set(hand):
        counts = {}
        for _, r in hand:
            if r >= 10:
                counts[r] = counts.get(r, 0) + 1
        vals = [(n, r) for r, n in counts.items() if n >= 3]
        return max(vals, key=lambda x: (x[1], x[0])) if vals else None

    def _seq_score(seq):
        if not seq:
            return 0
        n = seq[0]
        return n if n <= 4 else 10 + (n - 5)

    def _set_score(st):
        if not st:
            return 0
        return 14 if st[0] >= 4 else 3

    def _control_score(hand):
        # Trick-taking proxy: high cards and top-card chains are especially valuable.
        rank_value = {7: 0.00, 8: 0.05, 9: 0.12, 10: 0.28, 11: 0.58, 12: 1.05, 13: 1.75, 14: 3.10}
        score = sum(rank_value[r] for _, r in hand)
        for s in SUITS:
            rs = {r for ss, r in hand if ss == s}
            chain = 0
            for r in range(14, 6, -1):
                if r in rs:
                    chain += 1
                else:
                    break
            score += chain * 0.70
            n = len(rs)
            if n >= 4:
                score += (n - 3) * 0.22
        return score

    def _hand_value(hand):
        # Proxy for total hand EV. Declaration strength is intentionally weighted heavily
        # because declarations can generate large scores/repique before trick play.
        plen, ppips, _ = _best_point(hand)
        seq = _best_sequence(hand)
        st = _best_set(hand)
        decl = plen * 2.1 + ppips * 0.025
        if seq:
            decl += _seq_score(seq) * 3.4 + seq[0] * 0.45 + seq[1] * 0.025
        if st:
            decl += _set_score(st) * 3.6 + st[1] * 0.03
        raw_decl_points = plen + _seq_score(seq) + _set_score(st)
        if raw_decl_points >= 20:
            decl += (raw_decl_points - 19) * 0.75
        return decl + _control_score(hand) * 1.45

    def _seed_for_state(gs, hand):
        x = 1469598103934665603
        for s, r in sorted(hand):
            x ^= (ord(s) * 31 + r)
            x = (x * 1099511628211) & ((1 << 64) - 1)
        x ^= (getattr(gs, "your_score", 0) + 257 * getattr(gs, "opponent_score", 0))
        x ^= (1 if gs.your_name == gs.elder else 7)
        return x

    # ------------------------------------------------------------------
    # Exchange phase
    # ------------------------------------------------------------------
    def _exchange_move(gs):
        hand = list(gs.your_hand)
        if gs.your_name == gs.elder:
            limit = min(5, len(hand))
        else:
            limit = min(gs.talon_remaining or 0, len(hand))
        if limit <= 0:
            return []

        unseen = [c for c in FULL_DECK if c not in hand]
        candidates = []
        avg_card_bonus = 0.65
        for d in range(limit + 1):
            for idxs in combinations(range(len(hand)), d):
                idxset = set(idxs)
                kept = [c for i, c in enumerate(hand) if i not in idxset]
                discard = [hand[i] for i in idxs]
                screen = _hand_value(kept) + d * avg_card_bonus
                screen -= 0.45 * sum(1 for c in discard if c[1] == 14)
                candidates.append((screen, discard, kept))

        candidates.sort(key=lambda x: x[0], reverse=True)
        top = candidates[:60]
        rng = random.Random(_seed_for_state(gs, hand))

        best_ev = -1e18
        best_discard = []
        for _, discard, kept in top:
            d = len(discard)
            if d == 0:
                ev = _hand_value(hand)
            else:
                samples = 64 if d >= 2 else min(len(unseen), 32)
                total = 0.0
                if d == 1 and len(unseen) <= 32:
                    for c in unseen:
                        total += _hand_value(kept + [c])
                    ev = total / len(unseen)
                else:
                    for _ in range(samples):
                        draw = rng.sample(unseen, d)
                        total += _hand_value(kept + draw)
                    ev = total / samples
            ev += len(discard) * 0.02
            if ev > best_ev:
                best_ev = ev
                best_discard = discard
        return list(best_discard)

    # ------------------------------------------------------------------
    # Declare phase
    # ------------------------------------------------------------------
    def _has_sequence(hand):
        return _best_sequence(hand) is not None

    def _has_set(hand):
        return _best_set(hand) is not None

    def _record_elder_claim(gs, m):
        # Only the younger player's view carries elder_claim, and only for the category
        # currently being decided. This is the ONLY way to learn an elder claim's exact
        # cards when the elder ends up losing that category -- a losing claim never shows
        # up in gs.declarations afterward, so this info is otherwise lost for good.
        if gs.your_name == gs.elder:
            return
        ec = getattr(gs, "elder_claim", None)
        if not ec:
            return
        kind = ec[0]
        if kind == "sequence":
            _, length, top, suit = ec
            for r in range(top - length + 1, top + 1):
                m["known_opp"].add((suit, r))
        elif kind == "set":
            _, count, rank = ec
            if count >= 4:
                for s in SUITS:
                    m["known_opp"].add((s, rank))
            elif count == 3:
                ours = {s for s, r in gs.your_hand if r == rank}
                if len(ours) == 1:
                    for s in SUITS:
                        if s not in ours:
                            m["known_opp"].add((s, rank))
        elif kind == "point":
            # Only (length, suit) is revealed, not exact ranks -- remember it as a soft
            # "opponent is long here" hint for lead selection during tricks.
            _, length, suit = ec
            m.setdefault("opp_suit_length_hint", {})[suit] = length

    def _declare_move(gs, m):
        cat = gs.declare_category
        hand = gs.your_hand
        _record_elder_claim(gs, m)
        # No penalty for an unsuccessful valid claim: point is never validated by the
        # engine, so always claim it; sequence/set are only claimed when actually held,
        # since claiming without one forfeits the match.
        if cat == "point":
            return ("claim", "point")
        if cat == "sequence":
            return ("claim", "sequence") if _has_sequence(hand) else "pass"
        if cat == "set":
            return ("claim", "set") if _has_set(hand) else "pass"
        return "pass"

    # ------------------------------------------------------------------
    # Trick phase
    # ------------------------------------------------------------------
    def _update_decl_knowledge(gs, m):
        # Only winning claims are public in this engine.
        for d in getattr(gs, "declarations", []) or []:
            if d.get("winner") != gs.opponent_name:
                continue
            claim = d.get("claim")
            if not claim:
                continue
            if claim[0] == "sequence":
                _, length, top, suit = claim
                for r in range(top - length + 1, top + 1):
                    m["known_opp"].add((suit, r))
            elif claim[0] == "set":
                _, count, rank = claim
                if count >= 4:
                    for s in SUITS:
                        m["known_opp"].add((s, rank))
                elif count == 3:
                    ours = {s for s, r in gs.your_hand if r == rank}
                    if len(ours) == 1:
                        for s in SUITS:
                            if s not in ours:
                                m["known_opp"].add((s, rank))

    def _comb(n, k):
        if k < 0 or n < 0 or k > n:
            return 0
        return math.comb(n, k)

    def _lead_win_probability(card, gs, m):
        hand = gs.your_hand
        opp_cards = len(hand)  # Both hands stay equal size throughout tricks.

        known_opp_remaining = set(m["known_opp"])
        known_count = len(known_opp_remaining)

        # Cards excluded from the "unknown" pool: our hand, our own already-played
        # cards, our own exchange discards, and opponent leads we've directly seen.
        dead = set(m.get("my_played", set())) | set(m.get("my_discards", set())) | set(m.get("opp_played", set()))
        pool = [c for c in FULL_DECK if c not in hand and c not in dead and c not in known_opp_remaining]
        N = len(pool)
        if N <= 0 or opp_cards <= 0:
            return 1.0

        s, r = card
        if s in m.get("opp_void", set()):
            return 1.0

        known_higher = [c for c in known_opp_remaining if c[0] == s and c[1] > r]
        higher = [c for c in pool if c[0] == s and c[1] > r]
        H = len(higher)
        if H == 0 and not known_higher:
            return 1.0

        # Only the unknown portion of the opponent's hand is drawn from `pool`; cards we
        # already know they hold are certain, not sampled.
        unknown_opp = max(0, opp_cards - known_count)
        msize = min(unknown_opp, N)
        denom = _comb(N, msize)
        if denom == 0:
            p = 0.5
        else:
            safe = _comb(N - H, msize) if N - H >= msize else 0
            p = safe / denom

        if known_higher:
            # Opponent certainly holds a beater but may still duck it; heavily unfavorable
            # rather than a guaranteed loss.
            p *= 0.12

        return p

    def _choose_lead(gs, m):
        hand = list(gs.your_hand)
        my_tricks = (gs.tricks_won or {}).get(gs.your_name, 0)
        opp_tricks = (gs.tricks_won or {}).get(gs.opponent_name, 0)
        total_done = my_tricks + opp_tricks
        remaining = 12 - total_done
        capot_alive = opp_tricks == 0
        need_majority = max(0, 7 - my_tricks)

        # Capot (+40) and pique (+30) stack when the opponent's hand_points is still 0
        # at the start of tricks -- a much bigger prize than any single trick.
        opp_deal_points = (getattr(gs, "hand_points", None) or {}).get(gs.opponent_name, 0)
        capot_and_pique_alive = capot_alive and opp_deal_points == 0

        suit_hint = m.get("opp_suit_length_hint", {})

        scored = []
        for c in hand:
            p = _lead_win_probability(c, gs, m)
            r = c[1]
            urgency = 1.0
            if capot_alive:
                urgency += 0.32
            if capot_and_pique_alive:
                urgency += 0.5
            if need_majority > 0 and need_majority >= max(1, remaining // 2):
                urgency += 0.22
            preservation_cost = (r - 7) * 0.013
            ace_bonus = 0.16 if r == 14 else 0.0
            score = p * urgency + ace_bonus - preservation_cost
            hinted_len = suit_hint.get(c[0], 0)
            if hinted_len >= 5:
                score -= 0.06 * (hinted_len - 4)
            scored.append((score, p, -r, c))
        scored.sort(reverse=True)
        return scored[0][3]

    def _choose_follow(gs, m):
        hand = list(gs.your_hand)
        lead_card = gs.current_trick[0][1]
        lead_suit, lead_rank = lead_card
        same = sorted((c for c in hand if c[0] == lead_suit), key=lambda c: c[1])
        if same:
            winners = [c for c in same if c[1] > lead_rank]
            if winners:
                return winners[0]
            return same[0]
        # Cannot follow: follower necessarily loses in this engine. Shed the lowest-value
        # card, preferring to void out of short suits first.
        suit_counts = {s: sum(1 for c in hand if c[0] == s) for s in SUITS}
        return min(hand, key=lambda c: ((c[1] - 7) * 1.0 + 0.18 * suit_counts[c[0]], c[1]))

    def _trick_move(gs, m):
        m.setdefault("opp_played", set())
        m.setdefault("my_played", set())
        _update_decl_knowledge(gs, m)

        if gs.current_trick:
            opp_card = gs.current_trick[0][1]
            m["known_opp"].discard(opp_card)
            m["opp_played"].add(opp_card)
            move = _choose_follow(gs, m)
        else:
            move = _choose_lead(gs, m)

        m["my_played"].add(move)
        return move

    # ------------------------------------------------------------------
    # Fallback
    # ------------------------------------------------------------------
    def _safe_fallback(gs):
        hand = list(gs.your_hand)
        if gs.phase == "exchange":
            return []
        if gs.phase == "declare":
            if gs.declare_category == "point":
                return ("claim", "point")
            if gs.declare_category == "sequence" and _has_sequence(hand):
                return ("claim", "sequence")
            if gs.declare_category == "set" and _has_set(hand):
                return ("claim", "set")
            return "pass"
        if gs.current_trick:
            suit = gs.current_trick[0][1][0]
            same = [c for c in hand if c[0] == suit]
            if same:
                return min(same, key=lambda c: c[1])
        return min(hand, key=lambda c: c[1])

    # ------------------------------------------------------------------
    # Persistent cross-call memory (opponent info tracked within a match).
    # Attached to the nextMove function object itself, since it's the only
    # thing guaranteed to stay alive between calls when nothing module-level
    # is allowed.
    # ------------------------------------------------------------------
    if not hasattr(nextMove, "_memory_store"):
        nextMove._memory_store = {}
    memory_store = nextMove._memory_store

    def _empty_memory(marker=None):
        return {
            "known_opp": set(),
            "opp_void": set(),
            "opp_played": set(),
            "my_played": set(),
            "my_discards": set(),
            "opp_suit_length_hint": {},
            "last_hand_marker": marker,
        }

    def _state_key(gs):
        return (gs.your_name, gs.opponent_name)

    def _mem(gs):
        key = _state_key(gs)
        m = memory_store.get(key)
        if m is None:
            m = _empty_memory()
            memory_store[key] = m
        return m

    def _reset_hand_memory(gs):
        memory_store[_state_key(gs)] = _empty_memory((gs.dealer, gs.your_score, gs.opponent_score))

    # ------------------------------------------------------------------
    # Entry point
    # ------------------------------------------------------------------
    try:
        if gameState.phase == "exchange":
            _reset_hand_memory(gameState)
            discard = _exchange_move(gameState)
            _mem(gameState)["my_discards"] = set(discard)
            return discard
        if gameState.phase == "declare":
            return _declare_move(gameState, _mem(gameState))
        return _trick_move(gameState, _mem(gameState))
    except Exception:
        # The tournament forfeits on exceptions. A guaranteed-legal fallback is preferable
        # to exposing any internal strategy error.
        return _safe_fallback(gameState)
