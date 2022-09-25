// A more generic version of TMSpec that is useful for supporting Macro Machines.
// The differences are:
//   * It takes input dir in LookupTrans.
//   * Transtion is generalized to support Infinite and complex Halting Transitions.
//   * Transition includes base_num_steps to keep track of # steps in the base machine.
//   * Scoring a configuration is generalized

include "defs.dfy"

abstract module TMSpecGenAbstract {
  import opened DirSpec

  type Symbol(==)
  type State(==)

  function method IsHalt?(state : State) : bool

  type TM
  function method BlankSymbol(tm : TM) : Symbol
  function method InitState(tm : TM) : State
  // TODO: We don't necessarily only have one halt state ...
  function method HaltState(tm : TM) : State
    ensures IsHalt?(HaltState(tm))

  // Transitions have been generalized to allow Infinite transitions,
  // add num_base_steps, etc.
  datatype Transition =
    // "Normal" transition (write symbol, move, change state)
    | Transition(symbol : Symbol, dir : Dir, state : State, num_base_steps : nat)
    // Infinite transition means that we detected the machine was infitite while
    // evaluating this transition (Ex: Inf repeat inside macro block).
    | InfiniteTrans
    // We gave up trying to simulate this transition (Ex: > max sim steps).
    | GaveUpTrans 

  method LookupTrans(tm : TM, state : State, symbol : Symbol, dir : Dir)
    returns (trans : Transition)
    requires !IsHalt?(state)


  // Scoring
  function method ScoreSymbol(symbol : Symbol) : nat
  function method ScoreState(state : State) : nat
}

module TMSpecGenNat refines TMSpecGenAbstract {
  import TMSpecNat

  type Symbol = TMSpecNat.Symbol
  type State = TMSpecNat.StateOrHalt
  type TM = TMSpecNat.TM

  function method IsHalt?(state : State) : bool {
    state.Halt?
  }
  function method BlankSymbol(tm : TM) : Symbol {
    TMSpecNat.BlankSymbol
  }
  function method InitState(tm : TM) : State {
    TMSpecNat.RunState(TMSpecNat.InitState)
  }
  function method HaltState(tm : TM) : State {
    TMSpecNat.Halt
  }

  method LookupTrans(tm : TM, state : State, symbol : Symbol, dir : Dir)
    returns (trans : Transition)
  {
    var base_trans := TMSpecNat.LookupTrans(tm, state.state, symbol);
    return Transition(base_trans.symbol, base_trans.dir,
                      base_trans.state, 1);
  }


  // Scoring
  function method ScoreSymbol(symbol : Symbol) : nat {
    TMSpecNat.ScoreSymbol(symbol)
  }
  function method ScoreState(state : State) : nat {
    0
  }
}