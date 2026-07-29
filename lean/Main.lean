/-
  Lux formal verification — entry point.

  `lux_correctness` conjoins results proved elsewhere in this corpus. It holds
  what it imports and nothing more, which is the only thing a top-level theorem
  can honestly do: `lake build` succeeding here means Lean checked each
  conjunct's proof, in its own module, from its own hypotheses.

  Both conjuncts rest on Lean's ambient logic alone — no axiom of ours — which
  `lean/axioms.py` reports per theorem. Deliberately absent:

  - Safety and liveness. `Consensus.safety` composes two axioms and needs
    `2 * alpha > n`, i.e. sampling more than half the network; in the
    sub-sampled regime the protocol runs, safety is probabilistic and no
    deterministic theorem of that shape holds. `Consensus.Liveness.liveness`
    applies the ten axioms that are its argument.
  - Post-quantum hardness. `Quasar.Consensus` reduces to hardness axioms: the
    reduction is checked, the assumptions are assumed.

  Maps to: the modules imported below.
-/

import Consensus.BFT

namespace Lux.Main

/-- Results this corpus proves outright, conjoined.

    An earlier version stated four conjuncts, of which
    `spreadBps * volumeUSD / 10000 ≥ 0` is true of every `Nat` and the fourth
    was `True`; it imported no consensus or crypto module while its header said
    "if this file compiles, consensus is safe and live" across ten libraries.
    Each conjunct now names a theorem proved in the module it comes from, so
    compilation depends on that proof rather than restating its statement. -/
theorem lux_correctness :
    -- Quorum intersection: two quorums each above 2n/3, with f < n/3 faulty,
    -- overlap in more than f nodes — so they share an honest one.
    (∀ n f : Nat, f < n / 3 → ∀ q1 q2 : Nat,
      q1 > 2 * n / 3 → q2 > 2 * n / 3 → q1 + q2 > n + f) ∧
    -- An honest majority of 2f+1 in 3f+1 nodes clears that threshold.
    (∀ f : Nat, 0 < f → 2 * f + 1 > 2 * (3 * f + 1) / 3) :=
  ⟨fun n f hf q1 q2 hq1 hq2 =>
     Consensus.BFT.quorum_intersection n f hf q1 q2 hq1 hq2,
   fun f hf => Consensus.BFT.honest_majority_sufficient f hf⟩

end Lux.Main
