def nextMove(gameState):
    hand = gameState.your_hand

    def suit_cards(suit):
        return [c for c in hand if c[0] == suit]

    def lowest(cards):
        return min(cards, key=lambda c: c[1])

    def highest(cards):
        return max(cards, key=lambda c: c[1])

    # =====================================================================
    # Bidding
    # =====================================================================
    if gameState.phase == "bid":
        # Probability any one specific unseen card is in the opponent's
        # hand (vs. the kitty) at bid time: 13 unseen opponent cards out
        # of 50 - 13 = 37 total unseen cards.
        p_opp = 13.0 / 37.0

        total = 0.0
        spade_ranks = []
        for suit in ["H", "D", "C", "S"]:
            ranks_held = sorted((c[1] for c in suit_cards(suit)), reverse=True)
            if suit == "S":
                spade_ranks = ranks_held
            if not ranks_held:
                continue
            held_set = set(ranks_held)
            suit_total = 0.0
            for r in ranks_held:
                missing_above = sum(1 for x in range(r + 1, 15) if x not in held_set)
                prob_wins = (1 - p_opp) ** missing_above
                if suit != "S":
                    prob_wins *= 0.85
                suit_total += prob_wins
            # Long-suit credit: once our top cards in a suit have cleared
            # the field, low cards in a long holding often become winners
            # too (the opponent tends to run out of that suit first).
            # Trump gets a bigger version of this since it can't be
            # outranked by any other suit.
            length = len(ranks_held)
            if suit == "S":
                if length > 5:
                    suit_total += (length - 5) * 0.6
            else:
                if length > 4:
                    suit_total += (length - 4) * 0.3
            total += suit_total

        # The raw probability sum above is systematically conservative --
        # empirically, actual tricks taken run well above it (missing a
        # bid costs 2x what an overtrick gains, so a bit of built-in
        # caution is right, but the raw formula undershoots by more than
        # that alone justifies). 1.5x was tuned against real matches to
        # balance making bids reliably against not leaving points unbid.
        bid = max(0, min(13, int(round(total * 1.5))))

        highest_rank = max((r for _, r in hand), default=0)
        hand_is_nil_safe = highest_rank <= 10 and len(spade_ranks) <= 2
        if bid == 0 and not hand_is_nil_safe:
            bid = 1
        return bid

    # =====================================================================
    # Playing
    # =====================================================================
    trick = gameState.current_trick
    bid = gameState.your_bid
    won = gameState.tricks_won.get(gameState.your_name, 0)
    want_to_win = bid > 0 and won < bid

    # Infer suits the opponent has shown void in: any completed trick
    # where they didn't follow the led suit (and it wasn't their lead).
    opponent = gameState.opponent_name
    known_void_suits = set()
    for t in gameState.trick_history:
        leader = t["leader"]
        plays = dict(t["plays"])
        if leader != opponent and opponent in plays:
            led_suit = plays[leader][0]
            played_suit = plays[opponent][0]
            if played_suit != led_suit:
                known_void_suits.add(led_suit)

    if not trick:
        # ---- Leading ----
        non_spades = [c for c in hand if c[0] != "S"]
        can_lead_spades = gameState.spades_broken or not non_spades

        if want_to_win:
            best_suit_cards = None
            for suit in ["H", "D", "C"]:
                cards = suit_cards(suit)
                if cards and (
                    best_suit_cards is None
                    or max(c[1] for c in cards) > max(c[1] for c in best_suit_cards)
                ):
                    best_suit_cards = cards
            if best_suit_cards:
                return highest(best_suit_cards)
            if can_lead_spades and suit_cards("S"):
                return highest(suit_cards("S"))
            return highest(hand)
        else:
            # Don't want to win: lead low and safe. Leading a suit the
            # opponent is void in guarantees we win regardless of rank
            # (they can only respond off-suit, which always loses), so
            # avoid known-void suits. Among the rest, prefer our SHORTEST
            # suit: a suit where we hold few cards is one the opponent
            # more likely still holds several cards in (possibly higher
            # ones), giving them a real chance to beat us. Leading our
            # longest suit is actually the opposite of safe -- it's the
            # suit the opponent is statistically most likely to be short
            # or void in.
            safe_non_spades = [c for c in non_spades if c[0] not in known_void_suits]
            pool = safe_non_spades if safe_non_spades else non_spades
            if pool:
                by_suit = {}
                for c in pool:
                    by_suit.setdefault(c[0], []).append(c)
                shortest_suit = min(by_suit.values(), key=len)
                return lowest(shortest_suit)
            return lowest(hand)

    # ---- Following ----
    lead_suit, lead_rank = trick[0][1]
    same_suit = suit_cards(lead_suit)

    if same_suit:
        winners = [c for c in same_suit if c[1] > lead_rank]
        if want_to_win and winners:
            return lowest(winners)
        return lowest(same_suit)

    # Void in the lead suit (lead_suit is not spades here, since if it
    # were and we held spades, same_suit above would be non-empty).
    spades = suit_cards("S")
    if want_to_win and spades:
        return lowest(spades)

    non_spades = [c for c in hand if c[0] != "S"]
    if non_spades:
        return lowest(non_spades)
    return lowest(hand)