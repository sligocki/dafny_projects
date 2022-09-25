module DirSpec {
  datatype Dir = Left | Right
  function method OtherDir(dir : Dir) : Dir {
    match dir
      case Left => Right
      case Right => Left
  }
}

// Basic types and constants used by TMs.
// We abstract this in order to allow different implementation details
// Ex: State, Symbol : nat or datatype Symbol = S0 | S1 or macro machine states
// and symbols.
abstract module TMSpecAbstract {
  import opened DirSpec

  type Symbol(==)
  type State(==)
  const BlankSymbol : Symbol
  const InitState : State

  // TM Transition Table
  datatype StateOrHalt = RunState(state : State) | Halt
  datatype Transition =
    Transition(symbol : Symbol, dir : Dir, state : StateOrHalt)
  type TM

  function method LookupTrans(tm : TM, state : State, symbol : Symbol) : Transition

  // Sigma "score" for each symbol on tape.
  function method ScoreSymbol(symbol : Symbol) : nat {
    if symbol == BlankSymbol
      then 0
      else 1
  }
}

abstract module TMDefsAbstract {
  import opened TMSpec : TMSpecAbstract

  // TM Tape
  type Tape = map<int, Symbol>
  const BlankTape : Tape := map[]

  function method ReadTape(tape : Tape, pos : int) : Symbol {
    if pos in tape then tape[pos] else BlankSymbol
  }

  // Return a new Tape with update written.
  function method WriteTape(tape : Tape, pos : int, val : Symbol) : Tape {
    tape[pos := val]
  }


  // TM Simulator
  datatype Config = Config(
    tape : Tape,
    pos : int,
    state : StateOrHalt,
    step_num : nat
  )

  const InitConfig : Config :=
    Config(
      tape := BlankTape,
      pos := 0,
      state := RunState(InitState),
      step_num := 0
    )

  function method Step(tm : TM, config : Config) : Config
    requires !config.state.Halt?
  {
    var cur_symbol := ReadTape(config.tape, config.pos);
    var trans := LookupTrans(tm, config.state.state, cur_symbol);
    Config(
      tape := WriteTape(config.tape, config.pos, trans.symbol),
      pos := match(trans.dir) {
        case Right => config.pos + 1
        case Left  => config.pos - 1
      },
      state := trans.state,
      step_num := config.step_num + 1
    )
  }

  function StepN(tm : TM, config : Config, num_steps : nat) : Config
    decreases num_steps
  {
    if num_steps == 0
    then
      config
    else
      var pre_config := StepN(tm, config, num_steps - 1);
      if pre_config.state.Halt?
      then
        pre_config
      else
        Step(tm, pre_config)
  }

  // A TM is a halting TM if, after some number of steps starting from the initial config, it halts.
  predicate TMHalts(tm: TM) {
    exists n : nat :: StepN(tm, InitConfig, n).state.Halt?
  }


  // Define Sigma "score" for TMs (# non-blank symbols on tape).
  // TODO: This is not correct.
  method ScoreTape(tape : Tape) returns (score : nat) {
    var total : nat := 0;
    var items := tape.Items;
    while items != {} {
      var item :| item in items;
      total := total + ScoreSymbol(item.1);
      // print "Walrus ", item.0, " => ", item.1, " ", ScoreSymbol(item.1), " ", total, "\n";
      items := items - {item};
    }
    return total;
  }
}


// Example realization using State, Symbol : nat.
module TMSpecNat refines TMSpecAbstract {
  type Symbol = nat
  type State = nat
  const BlankSymbol : Symbol := 0
  const InitState : State := 0

  datatype TransKey = TransKey(state : State, symbol : Symbol)
  type TM = map<TransKey, Transition>

  function method LookupTrans(tm : TM, state : State, symbol : Symbol) : Transition {
    var key := TransKey(state, symbol);
    // Defaults to 0RH. We don't intend to use default, but allow it for simplicity.
    if key in tm then tm[key] else Transition(BlankSymbol, Right, Halt)
  }

  // A TM is fully defined if it has a transition defined for every state x symbol pair and those
  // transitions are all to valid states and write valid symbols.
  predicate DefinedTM(tm : TM, num_states : nat, num_symbols : nat) {
    forall state : nat, symbol : nat :: state < num_states && symbol < num_symbols
      ==> var key := TransKey(state, symbol);
          key in tm &&
          var trans := LookupTrans(tm, state, symbol);
          (trans.state.Halt? || trans.state.state < num_states) &&
          trans.symbol < num_symbols
  }
}

module TMDefsNat refines TMDefsAbstract {
  import opened TMSpec = TMSpecNat
}
