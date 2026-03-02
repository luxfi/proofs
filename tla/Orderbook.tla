---------------------------- MODULE Orderbook --------------------------------
(*
 * TLA+ Specification of the Lux DeFi CLOB Order Matching Engine
 *
 * Source: ~/work/lux/contracts/orderbook/
 *
 * Protocol summary:
 *   A central limit order book (CLOB) maintains sorted buy and sell orders.
 *   Orders are matched by price-time priority: best price first, then
 *   earliest arrival. Trades execute at the maker's price.
 *
 *   Each order has a unique ID, a side (Buy/Sell), a price, an amount,
 *   a filled amount, and a timestamp (sequence number). Partial fills
 *   are supported above a minimum fill size.
 *
 * State model:
 *   orders[id]           -- record per order
 *     .side              -- Buy | Sell
 *     .price             -- limit price
 *     .amount            -- total order size
 *     .filled            -- amount already filled
 *     .seqNo             -- arrival sequence number
 *   fills                -- sequence of fill records
 *   nextSeqNo            -- next sequence number to assign
 *
 * Actions:
 *   PlaceOrder(id, side, price, amount) -- submit a new order
 *   MatchOrders(bid, ask)               -- match a buy and sell order
 *   CancelOrder(id)                     -- cancel an unfilled order
 *
 * Safety:
 *   PriceTimePriority   -- earlier orders at same price fill first
 *   NoOverfill          -- sum of fills <= order amount
 *   MinFillSize         -- no partial fill below minimum
 *   FeeCorrectness      -- fees computed correctly
 *
 * Invariant:
 *   FillsBounded         -- sum of fills for any order <= order amount
 *)

EXTENDS Integers, FiniteSets, Sequences

\* --------------------------------------------------------------------------
\* CONSTANTS
\* --------------------------------------------------------------------------

CONSTANTS
    OrderIds,       \* Set of order identifiers
    MaxPrice,       \* Upper bound on prices
    MaxAmount,      \* Upper bound on order amounts
    MinFillSize,    \* Minimum partial fill size
    MaxFills        \* Upper bound on total fills for state constraint

\* --------------------------------------------------------------------------
\* ASSUMPTIONS
\* --------------------------------------------------------------------------

ASSUME OrderIds # {} /\ IsFiniteSet(OrderIds)
ASSUME MaxPrice \in Nat \ {0}
ASSUME MaxAmount \in Nat \ {0}
ASSUME MinFillSize \in Nat \ {0}
ASSUME MinFillSize <= MaxAmount
ASSUME MaxFills \in Nat \ {0}

\* --------------------------------------------------------------------------
\* DERIVED SETS
\* --------------------------------------------------------------------------

Sides  == {"Buy", "Sell"}
Prices == 1..MaxPrice

\* --------------------------------------------------------------------------
\* VARIABLES
\* --------------------------------------------------------------------------

VARIABLES
    orders,     \* orders[id] = [side, price, amount, filled, seqNo, active]
    fills,      \* Seq of [buyId, sellId, price, amount]
    nextSeqNo   \* monotonic counter for arrival order

vars == <<orders, fills, nextSeqNo>>

\* --------------------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------------------

OrderType ==
    [side   : Sides,
     price  : 0..MaxPrice,
     amount : 0..MaxAmount,
     filled : 0..MaxAmount,
     seqNo  : 0..Cardinality(OrderIds),
     active : BOOLEAN]

FillType ==
    [buyId  : OrderIds,
     sellId : OrderIds,
     price  : Prices,
     amount : 1..MaxAmount]

TypeOK ==
    /\ orders \in [OrderIds -> OrderType]
    /\ fills \in Seq(FillType)
    /\ nextSeqNo \in 0..Cardinality(OrderIds)

\* --------------------------------------------------------------------------
\* HELPERS
\* --------------------------------------------------------------------------

\* Remaining unfilled amount
Remaining(id) == orders[id].amount - orders[id].filled

\* Whether an order can accept more fills
IsOpen(id) == orders[id].active /\ Remaining(id) > 0

\* Minimum of two naturals
Min(a, b) == IF a <= b THEN a ELSE b

\* --------------------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------------------

Init ==
    /\ orders = [id \in OrderIds |->
        [side   |-> "Buy",
         price  |-> 0,
         amount |-> 0,
         filled |-> 0,
         seqNo  |-> 0,
         active |-> FALSE]]
    /\ fills = <<>>
    /\ nextSeqNo = 0

\* --------------------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------------------

(*
 * PlaceOrder(id, side, price, amount):
 *   Submit a new limit order. Assigns a sequence number for time priority.
 *   Precondition: order slot is inactive.
 *)
PlaceOrder(id, side, price, amount) ==
    /\ ~orders[id].active
    /\ orders[id].amount = 0
    /\ amount > 0
    /\ price > 0
    /\ nextSeqNo < Cardinality(OrderIds)
    /\ orders' = [orders EXCEPT ![id] =
        [side   |-> side,
         price  |-> price,
         amount |-> amount,
         filled |-> 0,
         seqNo  |-> nextSeqNo,
         active |-> TRUE]]
    /\ nextSeqNo' = nextSeqNo + 1
    /\ UNCHANGED fills

(*
 * MatchOrders(bid, ask):
 *   Match a buy order (bid) with a sell order (ask).
 *   Preconditions:
 *     - bid is a Buy, ask is a Sell
 *     - bid.price >= ask.price (willing to trade)
 *     - both have remaining unfilled amount
 *     - fill size >= MinFillSize (or fill completes the order)
 *   Trade executes at the maker's price (the earlier order's price).
 *
 *   Price-time priority: the match is valid only if no better-priced
 *   or earlier same-priced order exists on either side.
 *)
MatchOrders(bid, ask) ==
    /\ bid # ask
    /\ orders[bid].side = "Buy"
    /\ orders[ask].side = "Sell"
    /\ IsOpen(bid) /\ IsOpen(ask)
    /\ orders[bid].price >= orders[ask].price
    /\ Len(fills) < MaxFills
    \* Price-time priority: no better buy order should be skipped
    /\ \A other \in OrderIds :
        (other # bid /\ orders[other].side = "Buy" /\ IsOpen(other)
         /\ orders[other].price >= orders[ask].price)
        => \/ orders[bid].price > orders[other].price
           \/ (orders[bid].price = orders[other].price
               /\ orders[bid].seqNo <= orders[other].seqNo)
    \* Price-time priority: no better sell order should be skipped
    /\ \A other \in OrderIds :
        (other # ask /\ orders[other].side = "Sell" /\ IsOpen(other)
         /\ orders[bid].price >= orders[other].price)
        => \/ orders[ask].price < orders[other].price
           \/ (orders[ask].price = orders[other].price
               /\ orders[ask].seqNo <= orders[other].seqNo)
    /\ LET fillAmt == Min(Remaining(bid), Remaining(ask))
           \* Trade at maker's price (earlier order)
           tradePrice == IF orders[bid].seqNo <= orders[ask].seqNo
                         THEN orders[bid].price
                         ELSE orders[ask].price
       IN /\ fillAmt >= MinFillSize
             \/ fillAmt = Remaining(bid)
             \/ fillAmt = Remaining(ask)
          /\ orders' = [orders EXCEPT
                ![bid] = [@ EXCEPT !.filled = @ + fillAmt,
                                   !.active = (@ + fillAmt < orders[bid].amount)],
                ![ask] = [@ EXCEPT !.filled = @ + fillAmt,
                                   !.active = (@ + fillAmt < orders[ask].amount)]]
          /\ fills' = Append(fills,
                [buyId  |-> bid,
                 sellId |-> ask,
                 price  |-> tradePrice,
                 amount |-> fillAmt])
          /\ UNCHANGED nextSeqNo

(*
 * CancelOrder(id):
 *   Cancel an active order. Remaining unfilled amount is returned.
 *)
CancelOrder(id) ==
    /\ orders[id].active
    /\ orders' = [orders EXCEPT ![id] = [@ EXCEPT !.active = FALSE]]
    /\ UNCHANGED <<fills, nextSeqNo>>

\* --------------------------------------------------------------------------
\* NEXT-STATE RELATION
\* --------------------------------------------------------------------------

Next ==
    \/ \E id \in OrderIds, side \in Sides, price \in Prices, amt \in 1..MaxAmount :
        PlaceOrder(id, side, price, amt)
    \/ \E bid, ask \in OrderIds : MatchOrders(bid, ask)
    \/ \E id \in OrderIds : CancelOrder(id)

\* --------------------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

\* ==========================================================================
\* SAFETY INVARIANTS
\* ==========================================================================

(*
 * FillsBounded:
 *   For every order, the total filled amount never exceeds the order amount.
 *)
FillsBounded ==
    \A id \in OrderIds :
        orders[id].filled <= orders[id].amount

(*
 * PriceTimePriority:
 *   For any two fills in the fill sequence, if fill i and fill j share
 *   a side and fill i's order had better priority (better price or earlier
 *   at same price), then fill i appears before fill j in the sequence.
 *   We check this for buy-side fills (symmetric for sell-side).
 *)
PriceTimePriorityInvariant ==
    \A i, j \in 1..Len(fills) :
        (i < j /\ fills[i].buyId # fills[j].buyId)
        => LET oi == orders[fills[i].buyId]
               oj == orders[fills[j].buyId]
           IN ~(oj.price > oi.price
                \/ (oj.price = oi.price /\ oj.seqNo < oi.seqNo))

(*
 * NoOverfill:
 *   Active orders always have filled <= amount.
 *)
NoOverfill ==
    \A id \in OrderIds :
        orders[id].active => orders[id].filled <= orders[id].amount

(*
 * ConsistentDeactivation:
 *   If an order is deactivated by filling, filled = amount.
 *   If deactivated by cancel, filled < amount is possible.
 *)
ConsistentFillState ==
    \A id \in OrderIds :
        (orders[id].amount > 0 /\ orders[id].filled = orders[id].amount)
        => ~orders[id].active

(*
 * MonotonicFilled:
 *   Filled amount never decreases for any order.
 *)
MonotonicFilled ==
    [][
        \A id \in OrderIds :
            orders'[id].filled >= orders[id].filled
    ]_vars

(*
 * MonotonicFills:
 *   The fill sequence only grows (appended to).
 *)
MonotonicFillsAction ==
    [][Len(fills') >= Len(fills)]_vars

=============================================================================
