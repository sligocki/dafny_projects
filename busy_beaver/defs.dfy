
// Basic types and constants of Turing Machine Transition table
// TODO: Allow these to be generic so that we can use them for Macro Machines
type Symbol = nat
type State = nat
datatype Dir = Left | Right
const BlankSymbol : Symbol := 0
const InitState : State := 0

datatype StateOrHalt = RunState(state : State) | Halt

// TM Tape
datatype Tape = Tape(
  data : map<int, Symbol>,
  init_symbol : Symbol
)

function method BlankTape(init_symbol : Symbol) : Tape {
  Tape(data := map[], init_symbol := init_symbol)
}

function ReadTape(tape : Tape, pos : int) : Symbol {
  if pos in tape.data then tape.data[pos] else tape.init_symbol
}

// Return a new Tape with update written.
function WriteTape(tape : Tape, pos : int, val : Symbol) : Tape {
  Tape(data := tape.data[pos := val],
        init_symbol := tape.init_symbol)
}


// TM Transition Table
datatype TransKey = TransKey(state : State, symbol : Symbol)
datatype Transition =
  Transition(symbol : Symbol, dir : Dir, state : StateOrHalt)
type TM = map<TransKey, Transition>

function LookupTrans(tm : TM, state : State, symbol : Symbol) : Transition {
  var key := TransKey(state, symbol);
  // Defaults to 1RH (Do we need defaults?)
  if key in tm then tm[key] else Transition(1, Right, Halt)
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


// TM Simulator
datatype Config = Config(
  tape : Tape,
  pos : int,
  state : StateOrHalt,
  step_num : nat
)

const InitConfig : Config :=
  Config(
    tape := BlankTape(BlankSymbol),
    pos := 0,
    state := RunState(InitState),
    step_num := 0
  )

function Step(tm : TM, config : Config) : Config
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
  if (config.state.Halt? || num_steps == 0)
  then
    config
  else
    StepN(tm, Step(tm, config), num_steps - 1)
}

// A TM is a halting TM if, after some number of steps starting from the initial config, it halts.
predicate TMHalts(tm: TM) {
  exists n : nat :: StepN(tm, InitConfig, n).state.Halt?
}
