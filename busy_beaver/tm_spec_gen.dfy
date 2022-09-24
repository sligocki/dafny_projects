// A more generic version of TMSpec that is useful for supporting Macro Machines.
// The differences are:
//   * It takes input dir in LookupTrans.
//   * Transtion is generalized to support Infinite and complex Halting Transitions.
//   * Transition includes base_num_steps to keep track of # steps in the base machine.
//   * Scoring a configuration is generalized

include "defs.dfy"

abstract module TMSpecGenAbstract {
  type Symbol(==)
  type State(==)

  function method IsHalt?(state : State) : bool

  datatype Dir = Left | Right
  function method OtherDir(dir : Dir) : Dir {
    match dir
      case Left => Right
      case Right => Left
  }

  type TM
  function method BlankSymbol(tm : TM) : Symbol
  function method InitState(tm : TM) : State
  // TODO: We don't necessarily only have one halt state ...
  function method HaltState(tm : TM) : State
    ensures IsHalt?(HaltState(tm))

  // Transitions have been generalized to allow Infinite transitions,
  // add num_base_steps, etc.
  datatype Transition =
    | InfiniteTrans  // TODO: Add parameters
    | Transition(symbol : Symbol, dir : Dir, state : State, num_base_steps : nat)

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

  // TODO: ... there must be a better way!
  function method Dir2Dir(dir : TMSpecNat.Dir) : Dir {
    match dir
      case Left => Left
      case Right => Right
  }

  method LookupTrans(tm : TM, state : State, symbol : Symbol, dir : Dir)
    returns (trans : Transition)
  {
    var base_trans := TMSpecNat.LookupTrans(tm, state.state, symbol);
    return Transition(base_trans.symbol, Dir2Dir(base_trans.dir),
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